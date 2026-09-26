# -*- coding: utf-8 -*-
"""Chizi Digital Life 1.0 -- the smallest way in.

Builds one blank Chizi from the formal entry, feeds it a few legal frames of a
plain numeric reality, and prints what it holds at the end.

    python run_chizi.py

Nothing is loaded: no saved life, no knowledge, no file on disk.  This only
shows that the released sources start, run and stop on their own, starting from
a blank Chizi.

The state is read through the Life's own public readings: `las_view()`,
`action()`, `express()`, and the counts the Life itself keeps.
"""

import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from src import life_growth                      # noqa: E402
from src.life_growth import new_life             # noqa: E402

CHANNELS = 6        # how many channels the inlet of this Chizi has
MOMENTS = 8         # how many moments to run


def frame_at(t):
    """One legal frame: a number for every channel of the inlet."""
    return [round(math.sin(0.11 * (t + 1) * (c + 1)), 6)
            for c in range(CHANNELS)]


def brief(value):
    """How much of it there is, when that makes sense."""
    try:
        return len(value)
    except TypeError:
        return value


def main():
    print("Chizi Digital Life 1.0")
    print("  running from   %s" % os.path.dirname(life_growth.__file__))
    print("  a fresh Chizi, %d channels, %d moments" % (CHANNELS, MOMENTS))

    chizi = new_life(CHANNELS)

    for t in range(MOMENTS):
        chizi.step(frame_at(t), 1)               # src = 1: reality itself
        chizi.set_behavior([0.0] * chizi.behavior_count)

    print("  age            %d" % int(chizi.age))
    print("  connections    %d" % len(chizi.cn_pre))
    print("  elements       %d" % len(chizi.el_ends))
    print("  structures     %d" % len(chizi.st_ids))
    print("  behaviour ends %d" % int(chizi.behavior_count))

    las = chizi.las_view()
    print("  las            %s"
          % ", ".join("%s %s" % (k, brief(las[k])) for k in sorted(las)))

    act = list(chizi.action())
    print("  action         %d values, first %s"
          % (len(act), [round(x, 4) for x in act[:3]]))

    said = chizi.express(top=3)
    print("  organ says     %s (it has met no form yet)" % (said,))

    print("  it started, ran and stopped on its own.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
