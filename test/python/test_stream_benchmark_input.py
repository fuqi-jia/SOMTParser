"""Compressed benchmark transport must validate the entire input stream."""
import bz2
import gzip
import hashlib
import io
import json
import lzma
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from stream_benchmark_input import stream_source


XML = b'<instance format="XCSP3" type="CSP"><variables><var id="x">0 1</var></variables></instance>\n'


@pytest.mark.parametrize('suffix,encode', [
    ('.xml', lambda data: data), ('.xml.gz', gzip.compress), ('.xml.bz2', bz2.compress),
    ('.xml.xz', lzma.compress), ('.xml.lzma', lambda data: lzma.compress(data, format=lzma.FORMAT_ALONE)),
    ('.XML.GZ', gzip.compress),
])
def test_decoded_bytes_and_hash_match_source_for_each_transport(tmp_path, suffix, encode):
    source = tmp_path / ('source' + suffix)
    source.write_bytes(encode(XML))
    output = io.BytesIO()
    result = stream_source(source, output, tmp_path/'receipt.json')
    assert result['complete'] and output.getvalue() == XML
    assert result['decoded_bytes'] == len(XML)
    assert result['decoded_sha256'] == hashlib.sha256(XML).hexdigest()
    assert result == json.loads((tmp_path/'receipt.json').read_text())


@pytest.mark.parametrize('suffix,encode', [('.gz', gzip.compress), ('.xz', lzma.compress),
                                         ('.bz2', bz2.compress),
                                         ('.lzma', lambda d: lzma.compress(d, format=lzma.FORMAT_ALONE))])
def test_truncated_archive_cannot_receive_complete_receipt(tmp_path, suffix, encode):
    source = tmp_path / ('source.xml' + suffix)
    source.write_bytes(encode(XML)[:-4])
    result = stream_source(source, io.BytesIO(), tmp_path/'receipt.json')
    assert not result['complete'] and 'error' in result


def test_closed_consumer_cannot_receive_complete_receipt(tmp_path):
    class BrokenConsumer:
        def write(self, data):
            raise BrokenPipeError('converter exited')
    source = tmp_path/'source.xml'; source.write_bytes(XML)
    result = stream_source(source, BrokenConsumer(), tmp_path/'receipt.json')
    assert not result['complete'] and 'BrokenPipeError' in result['error']


@pytest.mark.parametrize('suffix,encode', [('.gz', gzip.compress), ('.xz', lzma.compress),
                                         ('.bz2', bz2.compress),
                                         ('.lzma', lambda d: lzma.compress(d, format=lzma.FORMAT_ALONE))])
def test_invalid_trailing_bytes_cannot_be_silently_discarded(tmp_path, suffix, encode):
    source = tmp_path / ('source.xml' + suffix)
    source.write_bytes(encode(XML) + b'invalid trailing bytes')
    result = stream_source(source, io.BytesIO(), tmp_path/'receipt.json')
    assert not result['complete'] and 'error' in result


@pytest.mark.parametrize('suffix,encode', [('.gz', gzip.compress), ('.xz', lzma.compress),
                                         ('.bz2', bz2.compress),
                                         ('.lzma', lambda d: lzma.compress(d, format=lzma.FORMAT_ALONE))])
def test_all_concatenated_members_are_decoded(tmp_path, suffix, encode):
    source = tmp_path / ('source.xml' + suffix)
    source.write_bytes(encode(XML[:20]) + encode(XML[20:]))
    output = io.BytesIO()
    result = stream_source(source, output, tmp_path/'receipt.json')
    assert result['complete'] and output.getvalue() == XML


@pytest.mark.parametrize('padding,ok', [(0, True), (4, True), (8, True), (3, False), (5, False)])
def test_xz_padding_between_and_after_members_is_checked(tmp_path, padding, ok):
    source = tmp_path/'source.xml.xz'
    source.write_bytes(lzma.compress(XML[:20]) + b'\0'*padding + lzma.compress(XML[20:]) + b'\0'*padding)
    output = io.BytesIO()
    result = stream_source(source, output, tmp_path/'receipt.json')
    assert result['complete'] is ok
    if ok:
        assert output.getvalue() == XML


@pytest.mark.parametrize('suffix,encode', [('.xz', lzma.compress), ('.bz2', bz2.compress),
                                         ('.lzma', lambda d: lzma.compress(d, format=lzma.FORMAT_ALONE))])
def test_decoder_drains_buffered_output_across_bounded_blocks(tmp_path, suffix, encode):
    data = XML * 40000
    source = tmp_path/('large.xml' + suffix); source.write_bytes(encode(data))
    output = io.BytesIO()
    result = stream_source(source, output, tmp_path/'receipt.json')
    assert result['complete'] and output.getvalue() == data


def test_xz_padding_can_span_input_blocks(tmp_path):
    source = tmp_path/'source.xml.xz'
    source.write_bytes(lzma.compress(XML[:20]) + b'\0'*(1024*1024) + lzma.compress(XML[20:]))
    output = io.BytesIO()
    result = stream_source(source, output, tmp_path/'receipt.json')
    assert result['complete'] and output.getvalue() == XML
