/*
 * Copyright (c) 2021 Joey Hwang
 *
 * This file is part of FFmpeg.
 *
 * FFmpeg is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * FFmpeg is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FFmpeg; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include "libavutil/avassert.h"
#include "libavutil/avstring.h"
#include "libavutil/bprint.h"
#include "libavutil/intreadwrite.h"
#include "libavutil/opt.h"
#include "libavutil/parseutils.h"
#include "libavutil/timestamp.h"
#include "avformat.h"
#include "internal.h"
#include "url.h"

typedef enum ConcatMatchMode {
    MATCH_ONE_TO_ONE,
    MATCH_EXACT_ID,
} ConcatMatchMode;

typedef struct ConcatStream {
    AVBSFContext *bsf;
    int out_stream_index;
} ConcatStream;

typedef struct {
    char *url;
    int64_t start_time;
    int64_t file_start_time;
    int64_t file_inpoint;
    int64_t duration;
    int64_t next_dts;
    ConcatStream *streams;
    AVDictionary *metadata;
    int nb_streams;
} ConcatFile;

typedef struct {
    AVClass *class;
    ConcatFile *files;
    ConcatFile *cur_file;
    unsigned nb_files;
    AVFormatContext *avf;
    int safe;
    int eof;
    ConcatMatchMode stream_match_mode;
    unsigned auto_convert;
    int segment_time_metadata;
    int64_t prev_start_time;
    int64_t prev_duration;
} ConcatContext;

static int concat_probe(const AVProbeData *probe)
{
    return memcmp(probe->buf, "ffconcat version 1.0", 20) ?
           0 : AVPROBE_SCORE_MAX;
}

static char *get_keyword(uint8_t **cursor)
{
    char *ret = *cursor += strspn(*cursor, SPACE_CHARS);
    *cursor += strcspn(*cursor, SPACE_CHARS);
    if (**cursor) {
        *((*cursor)++) = 0;
        *cursor += strspn(*cursor, SPACE_CHARS);
    }
    return ret;
}

static int safe_filename(const char *f)
{
    const char *start = f;

    for (; *f; f++) {
        /* A-Za-z0-9_- */
        if (!((unsigned)((*f | 32) - 'a') < 26 ||
              (unsigned)(*f - '0') < 10 || *f == '_' || *f == '-')) {
            if (f == start)
                return 0;
            else if (*f == '/')
                start = f + 1;
            else if (*f != '.')
                return 0;
        }
    }
    return 1;
}

#define FAIL(retcode) do { ret = (retcode); goto fail; } while(0)

static int add_file(AVFormatContext *avf, char *filename, ConcatFile **rfile,
                    unsigned *nb_files_alloc)
{
    ConcatContext *cat = avf->priv_data;
    ConcatFile *file;
    char *url = NULL;
    const char *proto;
    const char *ptr;
    size_t url_len;
    int ret;

    if (cat->safe > 0 && !safe_filename(filename)) {
        av_log(avf, AV_LOG_ERROR, "Unsafe file name '%s'\n", filename);
        FAIL(AVERROR(EPERM));
    }

    proto = avio_find_protocol_name(filename);
    if (proto && av_strstart(filename, proto, &ptr) &&
        (*ptr == ':' || *ptr == ',')) {
        url = filename;
        filename = NULL;
    } else {
        url_len = strlen(avf->url) + strlen(filename) + 16;
        if (!(url = av_malloc(url_len)))
            FAIL(AVERROR(ENOMEM));
        ff_make_absolute_url(url, url_len, avf->url, filename);
        av_freep(&filename);
    }

    // 최초 1회 할당
    if (!cat->files)
    {
        ConcatFile *new_files = av_malloc(sizeof(*cat->files));
        if(!new_files)
            FAIL(AVERROR(ENOMEM));
        cat->files = new_files;
        *nb_files_alloc = 1;
    }

    // concatpipe 에서는 하나의 file만 유지
    file = cat->files;
    memset(file, 0, sizeof(*file));
    *rfile = file;
    ++cat->nb_files;
    
    file->url        = url;
    file->start_time = AV_NOPTS_VALUE;
    file->duration   = AV_NOPTS_VALUE;
    file->next_dts   = AV_NOPTS_VALUE;

    return 0;

fail:
    av_free(url);
    av_free(filename);
    return ret;
}

static int copy_stream_props(AVStream *st, AVStream *source_st)
{
    int ret;

    if (st->codecpar->codec_id || !source_st->codecpar->codec_id) {
        if (st->codecpar->extradata_size < source_st->codecpar->extradata_size) {
            ret = ff_alloc_extradata(st->codecpar,
                                     source_st->codecpar->extradata_size);
            if (ret < 0)
                return ret;
        }
        memcpy(st->codecpar->extradata, source_st->codecpar->extradata,
               source_st->codecpar->extradata_size);
        return 0;
    }
    if ((ret = avcodec_parameters_copy(st->codecpar, source_st->codecpar)) < 0)
        return ret;
    st->r_frame_rate        = source_st->r_frame_rate;
    st->avg_frame_rate      = source_st->avg_frame_rate;
    st->sample_aspect_ratio = source_st->sample_aspect_ratio;
    avpriv_set_pts_info(st, 64, source_st->time_base.num, source_st->time_base.den);

    av_dict_copy(&st->metadata, source_st->metadata, 0);
    return 0;
}

static int detect_stream_specific(AVFormatContext *avf, int idx)
{
    ConcatContext *cat = avf->priv_data;
    AVStream *st = cat->avf->streams[idx];
    ConcatStream *cs = &cat->cur_file->streams[idx];
    const AVBitStreamFilter *filter;
    AVBSFContext *bsf;
    int ret;

    if (cat->auto_convert && st->codecpar->codec_id == AV_CODEC_ID_H264) {
        if (!st->codecpar->extradata_size                                                ||
            (st->codecpar->extradata_size >= 3 && AV_RB24(st->codecpar->extradata) == 1) ||
            (st->codecpar->extradata_size >= 4 && AV_RB32(st->codecpar->extradata) == 1))
            return 0;
        av_log(cat->avf, AV_LOG_INFO,
               "Auto-inserting h264_mp4toannexb bitstream filter\n");
        filter = av_bsf_get_by_name("h264_mp4toannexb");
        if (!filter) {
            av_log(avf, AV_LOG_ERROR, "h264_mp4toannexb bitstream filter "
                   "required for H.264 streams\n");
            return AVERROR_BSF_NOT_FOUND;
        }
        ret = av_bsf_alloc(filter, &bsf);
        if (ret < 0)
            return ret;
        cs->bsf = bsf;

        ret = avcodec_parameters_copy(bsf->par_in, st->codecpar);
        if (ret < 0)
           return ret;

        ret = av_bsf_init(bsf);
        if (ret < 0)
            return ret;

        ret = avcodec_parameters_copy(st->codecpar, bsf->par_out);
        if (ret < 0)
            return ret;
    }
    return 0;
}

static int match_streams_one_to_one(AVFormatContext *avf)
{
    ConcatContext *cat = avf->priv_data;
    AVStream *st;
    int i, ret;

    for (i = cat->cur_file->nb_streams; i < cat->avf->nb_streams; i++) {
        if (i < avf->nb_streams) {
            st = avf->streams[i];
        } else {
            if (!(st = avformat_new_stream(avf, NULL)))
                return AVERROR(ENOMEM);
        }
        if ((ret = copy_stream_props(st, cat->avf->streams[i])) < 0)
            return ret;
        cat->cur_file->streams[i].out_stream_index = i;
    }
    return 0;
}

static int match_streams_exact_id(AVFormatContext *avf)
{
    ConcatContext *cat = avf->priv_data;
    AVStream *st;
    int i, j, ret;

    for (i = cat->cur_file->nb_streams; i < cat->avf->nb_streams; i++) {
        st = cat->avf->streams[i];
        for (j = 0; j < avf->nb_streams; j++) {
            if (avf->streams[j]->id == st->id) {
                av_log(avf, AV_LOG_VERBOSE,
                       "Match slave stream #%d with stream #%d id 0x%x\n",
                       i, j, st->id);
                if ((ret = copy_stream_props(avf->streams[j], st)) < 0)
                    return ret;
                cat->cur_file->streams[i].out_stream_index = j;
            }
        }
    }
    return 0;
}

static int match_streams(AVFormatContext *avf)
{
    ConcatContext *cat = avf->priv_data;
    ConcatStream *map;
    int i, ret;

    if (cat->cur_file->nb_streams >= cat->avf->nb_streams)
        return 0;
    map = av_realloc(cat->cur_file->streams,
                     cat->avf->nb_streams * sizeof(*map));
    if (!map)
        return AVERROR(ENOMEM);
    cat->cur_file->streams = map;
    memset(map + cat->cur_file->nb_streams, 0,
           (cat->avf->nb_streams - cat->cur_file->nb_streams) * sizeof(*map));

    for (i = cat->cur_file->nb_streams; i < cat->avf->nb_streams; i++) {
        map[i].out_stream_index = -1;
        if ((ret = detect_stream_specific(avf, i)) < 0)
            return ret;
    }
    switch (cat->stream_match_mode) {
    case MATCH_ONE_TO_ONE:
        ret = match_streams_one_to_one(avf);
        break;
    case MATCH_EXACT_ID:
        ret = match_streams_exact_id(avf);
        break;
    default:
        ret = AVERROR_BUG;
    }
    if (ret < 0)
        return ret;
    cat->cur_file->nb_streams = cat->avf->nb_streams;
    return 0;
}

static int64_t get_best_effort_duration(ConcatFile *file, AVFormatContext *avf)
{
    if (avf->duration > 0)
        return avf->duration - (file->file_inpoint - file->file_start_time);
    if (file->next_dts != AV_NOPTS_VALUE)
        return file->next_dts - file->file_inpoint;
    return AV_NOPTS_VALUE;
}

static int open_file(AVFormatContext *avf, unsigned fileno)
{
    ConcatContext *cat = avf->priv_data;
    ConcatFile *file = cat->files;
    int ret;

    if (cat->avf)
        avformat_close_input(&cat->avf);

    cat->avf = avformat_alloc_context();
    if (!cat->avf)
        return AVERROR(ENOMEM);

    cat->avf->flags |= avf->flags & ~AVFMT_FLAG_CUSTOM_IO;
    cat->avf->interrupt_callback = avf->interrupt_callback;

    if ((ret = ff_copy_whiteblacklists(cat->avf, avf)) < 0)
        return ret;

    if ((ret = avformat_open_input(&cat->avf, file->url, NULL, NULL)) < 0 ||
        (ret = avformat_find_stream_info(cat->avf, NULL)) < 0) {
        av_log(avf, AV_LOG_ERROR, "Impossible to open '%s'\n", file->url);
        avformat_close_input(&cat->avf);
        return ret;
    }
    cat->cur_file = file;
    cat->prev_start_time = file->start_time = !fileno ? 0 :
                       cat->prev_start_time +
                       cat->prev_duration;
    file->file_start_time = (cat->avf->start_time == AV_NOPTS_VALUE) ? 0 : cat->avf->start_time;
    file->file_inpoint = file->file_start_time;
    cat->prev_duration = file->duration = get_best_effort_duration(file, cat->avf);

    if (cat->segment_time_metadata) {
        av_dict_set_int(&file->metadata, "lavf.concatdec.start_time", file->start_time, 0);
        if (file->duration != AV_NOPTS_VALUE)
            av_dict_set_int(&file->metadata, "lavf.concatdec.duration", file->duration, 0);
    }

    if ((ret = match_streams(avf)) < 0)
        return ret;
    return 0;
}

static int concat_read_close(AVFormatContext *avf)
{
    ConcatContext *cat = avf->priv_data;
    unsigned j;

    if (cat && cat->files)
    {
        av_freep(&cat->files->url);
        for (j = 0; j < cat->files->nb_streams; j++) {
            if (cat->files->streams[j].bsf)
                av_bsf_free(&cat->files->streams[j].bsf);
        }
        av_freep(&cat->files->streams);
        av_dict_free(&cat->files->metadata);
    }
    if (cat->avf)
        avformat_close_input(&cat->avf);
    av_freep(&cat->files);
    return 0;
}

static int concat_read_header(AVFormatContext *avf)
{
    ConcatContext *cat = avf->priv_data;
    AVBPrint bp;
    uint8_t *cursor, *keyword;
    int line = 0;
    unsigned nb_files_alloc = 0;
    ConcatFile *file = NULL;
    int64_t ret;

    av_bprint_init(&bp, 0, AV_BPRINT_SIZE_UNLIMITED);

    while ((ret = ff_read_line_to_bprint_overwrite(avf->pb, &bp)) >= 0) {
        line++;
        cursor = bp.str;
        keyword = get_keyword(&cursor);
        if (!*keyword || *keyword == '#')
            continue;

        if (!strcmp(keyword, "file")) {
            char *filename = av_get_token((const char **)&cursor, SPACE_CHARS);
            if (!filename) {
                av_log(avf, AV_LOG_ERROR, "Line %d: filename required\n", line);
                FAIL(AVERROR_INVALIDDATA);
            }
            if ((ret = add_file(avf, filename, &file, &nb_files_alloc)) < 0)
                goto fail;
            break;
        } else if (!strcmp(keyword, "file_packet_metadata")) {
            char *metadata;
            if (!file) {
                av_log(avf, AV_LOG_ERROR, "Line %d: %s without file\n",
                       line, keyword);
                FAIL(AVERROR_INVALIDDATA);
            }
            metadata = av_get_token((const char **)&cursor, SPACE_CHARS);
            if (!metadata) {
                av_log(avf, AV_LOG_ERROR, "Line %d: packet metadata required\n", line);
                FAIL(AVERROR_INVALIDDATA);
            }
            if ((ret = av_dict_parse_string(&file->metadata, metadata, "=", "", 0)) < 0) {
                av_log(avf, AV_LOG_ERROR, "Line %d: failed to parse metadata string\n", line);
                av_freep(&metadata);
                FAIL(AVERROR_INVALIDDATA);
            }
            av_freep(&metadata);
        } else if (!strcmp(keyword, "stream")) {
            if (!avformat_new_stream(avf, NULL))
                FAIL(AVERROR(ENOMEM));
        } else if (!strcmp(keyword, "exact_stream_id")) {
            if (!avf->nb_streams) {
                av_log(avf, AV_LOG_ERROR, "Line %d: exact_stream_id without stream\n",
                       line);
                FAIL(AVERROR_INVALIDDATA);
            }
            avf->streams[avf->nb_streams - 1]->id =
                strtol(get_keyword(&cursor), NULL, 0);
        } else if (!strcmp(keyword, "ffconcat")) {
            char *ver_kw  = get_keyword(&cursor);
            char *ver_val = get_keyword(&cursor);
            if (strcmp(ver_kw, "version") || strcmp(ver_val, "1.0")) {
                av_log(avf, AV_LOG_ERROR, "Line %d: invalid version\n", line);
                FAIL(AVERROR_INVALIDDATA);
            }
            if (cat->safe < 0)
                cat->safe = 1;
        } else {
            av_log(avf, AV_LOG_ERROR, "Line %d: unknown keyword '%s'\n",
                   line, keyword);
            FAIL(AVERROR_INVALIDDATA);
        }
    }
    if (ret == AVERROR_EOF)
        goto fail;
    if (ret != AVERROR_EOF && ret < 0)
        goto fail;
    if (!cat->nb_files)
        FAIL(AVERROR_INVALIDDATA);

    cat->stream_match_mode = MATCH_ONE_TO_ONE;
    // cat->stream_match_mode = avf->nb_streams ? MATCH_EXACT_ID :
    //                                            MATCH_ONE_TO_ONE;
    if ((ret = open_file(avf, cat->nb_files - 1)) < 0)
        goto fail;

fail:
    av_bprint_finalize(&bp, NULL);
    return ret;
}

static int open_next_file(AVFormatContext *avf)
{
    ConcatContext *cat = avf->priv_data;
    // unsigned fileno = cat->cur_file - cat->files;

    cat->cur_file->duration = get_best_effort_duration(cat->cur_file, cat->avf);

    return concat_read_header(avf);
    // if (++fileno >= cat->nb_files) {
    //     cat->eof = 1;
    //     return AVERROR_EOF;
    // }
    // return open_file(avf, fileno);
}

static int filter_packet(AVFormatContext *avf, ConcatStream *cs, AVPacket *pkt)
{
    int ret;

    if (cs->bsf) {
        ret = av_bsf_send_packet(cs->bsf, pkt);
        if (ret < 0) {
            av_log(avf, AV_LOG_ERROR, "h264_mp4toannexb filter "
                   "failed to send input packet\n");
            return ret;
        }

        while (!ret)
            ret = av_bsf_receive_packet(cs->bsf, pkt);

        if (ret < 0 && (ret != AVERROR(EAGAIN) && ret != AVERROR_EOF)) {
            av_log(avf, AV_LOG_ERROR, "h264_mp4toannexb filter "
                   "failed to receive output packet\n");
            return ret;
        }
    }
    return 0;
}

static int concat_read_packet(AVFormatContext *avf, AVPacket *pkt)
{
    ConcatContext *cat = avf->priv_data;
    int ret;
    int64_t delta;
    ConcatStream *cs;
    AVStream *st;

    if (cat->eof)
        return AVERROR_EOF;

    if (!cat->avf)
        return AVERROR(EIO);

    while (1) {
        ret = av_read_frame(cat->avf, pkt);
        if (ret == AVERROR_EOF) {
            if ((ret = open_next_file(avf)) < 0)
                return ret;
            continue;
        }
        if (ret < 0)
            return ret;
        if ((ret = match_streams(avf)) < 0) {
            return ret;
        }
        cs = &cat->cur_file->streams[pkt->stream_index];
        if (cs->out_stream_index < 0) {
            av_packet_unref(pkt);
            continue;
        }
        break;
    }
    if ((ret = filter_packet(avf, cs, pkt)) < 0)
        return ret;

    st = cat->avf->streams[pkt->stream_index];
    av_log(avf, AV_LOG_DEBUG, "file:%d stream:%d pts:%s pts_time:%s dts:%s dts_time:%s",
           (unsigned)(cat->nb_files - 1), pkt->stream_index,
           av_ts2str(pkt->pts), av_ts2timestr(pkt->pts, &st->time_base),
           av_ts2str(pkt->dts), av_ts2timestr(pkt->dts, &st->time_base));

    // SIDX earliest_presentation_time과 관련
    // if (pkt->stream_index > 0)
    // {
    //     delta = av_rescale_q(-100000,
    //                         AV_TIME_BASE_Q,
    //                         cat->avf->streams[pkt->stream_index]->time_base);
    //     if (pkt->pts != AV_NOPTS_VALUE)
    //         pkt->pts += delta;
    //     if (pkt->dts != AV_NOPTS_VALUE)
    //         pkt->dts += delta;
    // }
    // delta = av_rescale_q(cat->cur_file->start_time - cat->cur_file->file_inpoint,
    //                      AV_TIME_BASE_Q,
    //                      cat->avf->streams[pkt->stream_index]->time_base);
    // if (pkt->pts != AV_NOPTS_VALUE)
    //     pkt->pts += delta;
    // if (pkt->dts != AV_NOPTS_VALUE)
    //     pkt->dts += delta;
    av_log(avf, AV_LOG_DEBUG, " -> pts:%s pts_time:%s dts:%s dts_time:%s\n",
           av_ts2str(pkt->pts), av_ts2timestr(pkt->pts, &st->time_base),
           av_ts2str(pkt->dts), av_ts2timestr(pkt->dts, &st->time_base));
    if (cat->cur_file->metadata) {
        size_t metadata_len;
        char* packed_metadata = av_packet_pack_dictionary(cat->cur_file->metadata, &metadata_len);
        if (!packed_metadata)
            return AVERROR(ENOMEM);
        ret = av_packet_add_side_data(pkt, AV_PKT_DATA_STRINGS_METADATA,
                                      packed_metadata, metadata_len);
        if (ret < 0) {
            av_freep(&packed_metadata);
            return ret;
        }
    }

    if (cat->cur_file->duration == AV_NOPTS_VALUE && st->internal->cur_dts != AV_NOPTS_VALUE) {
        int64_t next_dts = av_rescale_q(st->internal->cur_dts, st->time_base, AV_TIME_BASE_Q);
        if (cat->cur_file->next_dts == AV_NOPTS_VALUE || next_dts > cat->cur_file->next_dts) {
            cat->cur_file->next_dts = next_dts;
        }
    }

    pkt->stream_index = cs->out_stream_index;
    return 0;
}

#define OFFSET(x) offsetof(ConcatContext, x)
#define DEC AV_OPT_FLAG_DECODING_PARAM

static const AVOption options[] = {
    { "safe", "enable safe mode",
      OFFSET(safe), AV_OPT_TYPE_BOOL, {.i64 = 1}, -1, 1, DEC },
    { "auto_convert", "automatically convert bitstream format",
      OFFSET(auto_convert), AV_OPT_TYPE_BOOL, {.i64 = 1}, 0, 1, DEC },
    { "segment_time_metadata", "output file segment start time and duration as packet metadata",
      OFFSET(segment_time_metadata), AV_OPT_TYPE_BOOL, {.i64 = 0}, 0, 1, DEC },
    { NULL }
};

static const AVClass concatpipe_class = {
    .class_name = "concatpipe demuxer",
    .item_name  = av_default_item_name,
    .option     = options,
    .version    = LIBAVUTIL_VERSION_INT,
};


const AVInputFormat ff_concatpipe_demuxer = {
    .name           = "concatpipe",
    .long_name      = NULL_IF_CONFIG_SMALL("Modified virtual concatenation script"),
    .priv_data_size = sizeof(ConcatContext),
    .flags_internal = FF_FMT_INIT_CLEANUP,
    .read_probe     = concat_probe,
    .read_header    = concat_read_header,
    .read_packet    = concat_read_packet,
    .read_close     = concat_read_close,
    .priv_class     = &concatpipe_class,
};
