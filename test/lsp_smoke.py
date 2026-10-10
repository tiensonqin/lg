#!/usr/bin/env python3
# LSP smoke: init caps, didOpen/didChange diagnostic push, completion
# (builtins + module tops + require-alias members; degrades to builtins
# on a file with errors).
import json, subprocess, sys

p = subprocess.Popen([sys.argv[1], 'lsp'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)

def msg(o):
    b = json.dumps(o).encode()
    p.stdin.write(b'Content-Length: %d\r\n\r\n' % len(b) + b)
    p.stdin.flush()

def read():
    hdr = b''
    while b'\r\n\r\n' not in hdr:
        hdr += p.stdout.read(1)
    n = int(hdr.decode().split('Content-Length: ')[1].split('\r\n')[0])
    return json.loads(p.stdout.read(n))

fail = []
msg({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}})
caps = read()['result']['capabilities']
if 'completionProvider' not in caps:
    fail.append('no completionProvider cap')

msg({"jsonrpc": "2.0", "method": "textDocument/didOpen",
     "params": {"textDocument": {"uri": "file:///tmp/lsp_smoke.lg",
                                 "text": "(ns s (:require [qc]))\n(defn f [x] x)\n"}}})
r = read()
if r['params']['diagnostics'] != []:
    fail.append('clean file published diagnostics')

msg({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
     "params": {"textDocument": {"uri": "file:///tmp/lsp_smoke.lg"}, "position": {"line": 0, "character": 0}}})
items = read()['result']['items']
if not any(i['label'] == 'conj' for i in items):
    fail.append('missing builtin completion')
if not any(i['label'] == 'f' for i in items):
    fail.append('missing module topdef completion')
if not any(i['label'].startswith('qc/') for i in items):
    fail.append('missing require-alias completion')

msg({"jsonrpc": "2.0", "method": "textDocument/didChange",
     "params": {"textDocument": {"uri": "file:///tmp/lsp_smoke.lg"},
                "contentChanges": [{"text": "(ns s)\n(+ 1 \"a\")\n"}]}})
r = read()
d = r['params']['diagnostics']
if not d or not d[0]['code'].startswith('E1'):
    fail.append('no E1xx diagnostic on broken file')

msg({"jsonrpc": "2.0", "id": 3, "method": "textDocument/completion",
     "params": {"textDocument": {"uri": "file:///tmp/lsp_smoke.lg"}, "position": {"line": 0, "character": 0}}})
items = read()['result']['items']
if not items or not all(i['detail'] == 'builtin' for i in items):
    fail.append('degraded completion not builtin-only')

msg({"jsonrpc": "2.0", "id": 4, "method": "shutdown"})
p.kill()
if fail:
    print('FAIL(lsp):', '; '.join(fail))
    sys.exit(1)
print('ok lsp')
