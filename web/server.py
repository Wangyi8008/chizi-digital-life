# -*- coding: utf-8 -*-
"""Chizi Digital Life 1.0 -- a small local web interface.

One Life is shared by both pages.  There is exactly one instance here, and
every request works on it: the two pages are two ways of looking at the same
living thing, never two lives.

    /grow/    Growth / Teaching -- build a blank Chizi, give it reality and
              language forms, run it, look at what it holds, save and load it.
    /talk/    Dialogue / Interaction -- give it a language form, see what it
              really says back.

What this server does not do
    It never writes into the Life's own tables.  It cannot: it only calls the
    public entry points (`new_life`, `step`, `action`, `express`, `las_view`,
    `dump_life`, `load_life`).  Elements, connections and structures are formed
    by the Life itself, out of the reality and the forms it is given, or they
    are not formed at all.

    It does not pretend the Life can do what it cannot.  /talk/ shows what
    `express()` really returns -- at present an empty answer for the forms given
    here.  Recalling existing knowledge from a language form, and answering, are
    not yet verified to hold in Chizi 1.0; that empty answer is this Life's own
    present reading, not a statement that no recall can ever form.  There is no
    keyword matching, no canned reply, no language model behind the page.

    A life saved from here goes to `web/runtime/`, beside this file.  Nothing
    is shipped with the sources.

    python web/server.py        then open http://127.0.0.1:8765/
"""

import json
import os
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from src.life_growth import new_life, dump_life, load_life, RealityInlet  # noqa

PORT = int(os.environ.get("CHIZI_PORT", "8765"))
RUNTIME = os.path.join(HERE, "runtime")

_lock = threading.Lock()
_LIFE = {"life": None, "channels": 6}


# --------------------------------------------------------------------------
# the one Life, and what can be read off it


def _channels_now(life):
    """How many reality channels this Life takes.

    It is the count the Life was built with, or was loaded with.  Not the length
    of its own activity frame: that one is wider, because the behaviour ends and
    the Life's own place are carried in it too.
    """
    return _LIFE["channels"]


def _state(life):
    """Everything a page may show.  Read only."""
    las = life.las_view()
    return {
        "age": int(life.age),
        "channels": _channels_now(life),
        "behaviour_ends": int(life.behavior_count),
        "connections": len(life.cn_pre),
        "elements": len(life.el_ends),
        "structures": len(life.st_ids),
        "action": [round(float(x), 6) for x in life.action()],
        "says": list(life.express(top=3)),
        "las": dict((k, (len(v) if hasattr(v, "__len__") else v))
                    for k, v in las.items()),
    }


def _new(channels):
    channels = max(1, min(64, int(channels)))
    life = new_life(channels)
    _LIFE["life"] = life
    _LIFE["channels"] = channels
    return life


def _life():
    if _LIFE["life"] is None:
        _new(_LIFE["channels"])
    return _LIFE["life"]


def _numbers(text, count, what):
    """Read a comma separated list of numbers and insist on its length."""
    if isinstance(text, (list, tuple)):
        values = [float(x) for x in text]
    else:
        body = str(text or "").replace(",", " ").split()
        values = [float(x) for x in body] if body else []
    if not values:
        values = [0.0] * count
    if len(values) != count:
        raise ValueError("%s takes %d numbers, got %d" % (what, count, len(values)))
    return values


def _run(frame, change, moments, form):
    """Feed the Life `moments` frames, and let it take each one in.

    The teacher gives the reality and, at most, one language form per moment.
    Nothing else is done on its behalf.
    """
    life = _life()
    moments = max(1, min(5000, int(moments)))
    for t in range(moments):
        row = [frame[c] + t * change[c] for c in range(len(frame))]
        life.step(row, 1, form=(form or None))
        life.set_behavior([0.0] * life.behavior_count)
    return life


def _say(text, frame):
    """One whole language form in one moment, the reality standing beside it.

    The form goes in exactly as it was given: the whole string is one form, and
    one Send is one moment.  Nothing is split up, counted out or interpreted
    here.
    """
    life = _life()
    form = str(text or "")
    if not form:
        return life
    life.step(list(frame), 1, form=form)
    life.set_behavior([0.0] * life.behavior_count)
    return life


def _safe_name(name):
    """One clean file name for a saved life, with the .bin ending."""
    safe = "".join(c for c in str(name or "") if c.isalnum() or c in "-_.") or "life"
    if not safe.endswith(".bin"):
        safe += ".bin"
    return safe


def _save(name):
    life = _life()
    if not os.path.isdir(RUNTIME):
        os.makedirs(RUNTIME)
    safe = _safe_name(name)
    path = os.path.join(RUNTIME, safe)
    dump_life(life, path, meta={"channels": _channels_now(life)})
    return safe


def _load(name):
    safe = _safe_name(os.path.basename(str(name or "")))
    path = os.path.join(RUNTIME, safe)
    if not os.path.isfile(path):
        raise ValueError("no such saved life: %s" % safe)
    life, meta = load_life(path, RealityInlet(int(meta_channels(path))))
    _LIFE["life"] = life
    _LIFE["channels"] = int(meta_channels(path))
    return safe


def meta_channels(path):
    import struct
    with open(path, "rb") as fh:
        fh.read(8)
        size = struct.unpack(">Q", fh.read(8))[0]
        man = json.loads(fh.read(size).decode("utf-8"))
    return int((man.get("meta") or {}).get("channels") or 6)


def _saved():
    if not os.path.isdir(RUNTIME):
        return []
    return sorted(n for n in os.listdir(RUNTIME) if n.endswith(".bin"))


# --------------------------------------------------------------------------
# http


class Handler(BaseHTTPRequestHandler):
    server_version = "ChiziDigitalLife/1.0"

    def log_message(self, fmt, *args):
        pass                                    # keep the console quiet

    def _send(self, code, body, kind="application/json; charset=utf-8"):
        data = body if isinstance(body, bytes) else body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", kind)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _json(self, payload, code=200):
        self._send(code, json.dumps(payload, ensure_ascii=False))

    def _page(self, name):
        path = os.path.join(HERE, name)
        if not os.path.isfile(path):
            return self._send(404, "not found", "text/plain; charset=utf-8")
        with open(path, "rb") as fh:
            self._send(200, fh.read(), "text/html; charset=utf-8")

    def do_GET(self):
        route = self.path.split("?")[0]
        if route in ("/", "/index.html"):
            return self._page("index.html")
        if route in ("/grow", "/grow/"):
            return self._page("grow.html")
        if route in ("/talk", "/talk/"):
            return self._page("talk.html")
        if route == "/api/state":
            with _lock:
                return self._json(_state(_life()))
        if route == "/api/saved":
            return self._json({"saved": _saved()})
        return self._json({"error": "no such path: %s" % route}, 404)

    def do_POST(self):
        route = self.path.split("?")[0]
        length = int(self.headers.get("Content-Length") or 0)
        raw = self.rfile.read(length).decode("utf-8") if length else "{}"
        try:
            body = json.loads(raw or "{}")
        except ValueError:
            return self._json({"error": "the request body is not JSON"}, 400)

        try:
            with _lock:
                if route == "/api/new":
                    life = _new(body.get("channels", 6))
                    return self._json({"ok": True, "state": _state(life)})

                if route == "/api/run":
                    count = _channels_now(_life())
                    frame = _numbers(body.get("frame"), count, "the reality frame")
                    change = _numbers(body.get("change"), count, "the change per moment")
                    life = _run(frame, change, body.get("moments", 1),
                                body.get("form") or None)
                    return self._json({"ok": True, "state": _state(life)})

                if route == "/api/say":
                    count = _channels_now(_life())
                    frame = _numbers(body.get("frame"), count, "the reality frame")
                    life = _say(body.get("text", ""), frame)
                    return self._json({"ok": True, "state": _state(life)})

                if route == "/api/save":
                    return self._json({"ok": True, "saved": _save(body.get("name")),
                                       "saved_lives": _saved()})

                if route == "/api/load":
                    name = _load(body.get("name"))
                    return self._json({"ok": True, "loaded": name,
                                       "state": _state(_life())})
        except ValueError as exc:
            return self._json({"error": str(exc)}, 400)
        except Exception as exc:                 # keep the page alive and honest
            return self._json({"error": "%s: %s" % (type(exc).__name__, exc)}, 500)

        return self._json({"error": "no such path: %s" % route}, 404)


def main():
    server = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    print("Chizi Digital Life 1.0")
    print("  one Life, two pages, at http://127.0.0.1:%d/" % PORT)
    print("    /grow/   growth / teaching")
    print("    /talk/   dialogue / interaction")
    print("  a saved life goes to %s" % RUNTIME)
    print("  Ctrl-C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nstopped.")
    finally:
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
