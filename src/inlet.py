# -*- coding: utf-8 -*-

import math

__all__ = ["RealityInlet"]


class RealityInlet:
    def __init__(self, channel_count: int):
        if int(channel_count) < 1:
            raise ValueError("channel_count must be >= 1")
        self.channel_count = int(channel_count)

    def frame(self, samples):
        try:
            values = [float(x) for x in samples]
        except TypeError:
            raise ValueError("one reality frame must be an iterable of real samples")
        if len(values) != self.channel_count:
            raise ValueError(
                "frame length %d does not match carrier channel count %d" % (len(values), self.channel_count)
            )
        for v in values:
            if not math.isfinite(v):
                raise ValueError("samples must be finite real numbers")
        return values

    def silence(self):
        return [0.0] * self.channel_count

    def describe(self) -> str:
        return "RealityInlet(channel_count=%d)  # physical carrier, channels carry no semantics" % self.channel_count
