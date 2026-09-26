# -*- coding: utf-8 -*-

import math

try:
    from .dna import LifeDNA, Life
except ImportError:
    from dna import LifeDNA, Life                   # noqa: F401

__all__ = ["LifeDNA04", "LifeTissue"]


class LifeDNA04(LifeDNA):
    def __init__(self, mode_amp: float = 0.6, mode_rate: float = 0.0,
                 mode_baseline_ratio: float = 50.0, **kwargs):
        super().__init__(**kwargs)
        if mode_amp < 0.0:
            raise ValueError("mode_amp must be >= 0")
        if mode_rate < 0.0:
            raise ValueError("mode_rate must be >= 0")
        if mode_baseline_ratio < 1.0:
            raise ValueError("mode_baseline_ratio must be >= 1")
        self.mode_amp = float(mode_amp)
        self.mode_rate = float(mode_rate)
        self.mode_baseline_ratio = float(mode_baseline_ratio)

        self.mode_baseline_rate = float(mode_rate) / float(mode_baseline_ratio)

    def describe(self) -> str:
        return super().describe() + (
            " + tissue(mode_amp=%g, mode_rate=%g, baseline_ratio=%g, N dims, born all zero)"
            % (self.mode_amp, self.mode_rate, self.mode_baseline_ratio))

class LifeTissue(Life):
    def __init__(self, dna: LifeDNA04, inlet):
        super().__init__(dna, inlet)
        n = dna.state_size
        self.tissue = [0.0] * n
        self.tissue_baseline = [1.0 / n] * n
        self.tissue_enabled = True

    # ------------------------------------------------------------------
    def running_mode(self):
        amp = self.dna.mode_amp
        return [1.0 + amp * math.tanh(v) for v in self.tissue]

    # ------------------------------------------------------------------
    def step(self, frame):
        r = self.inlet.frame(frame)
        dna = self.dna
        s = self.state
        n = len(s)

        real_drive = dna.entry_drive(r)
        internal_drive = dna.internal_coupling(s)
        kappa = dna.kappa
        eta = dna.eta
        gamma = dna.gamma
        mode = self.running_mode()

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = real_drive[i] + kappa * internal_drive[i]
            drive_out[i] = drive
            new_state[i] = s[i] + eta * (math.tanh(drive) - gamma * mode[i] * s[i])

        acc = 0.0
        for i in range(n):
            diff = new_state[i] - s[i]
            acc += diff * diff
        delta = math.sqrt(acc)

        self.state = new_state
        self.last_drive = drive_out
        self.last_delta = delta
        self.change_baseline = ((1.0 - dna.baseline_rate) * self.change_baseline
                                + dna.baseline_rate * delta)
        self.age += 1

        self._write_tissue(drive_out)

        return {
            "tick": self.age,
            "delta": delta,
            "baseline": self.change_baseline,
            "same_or_different": delta - self.change_baseline,
        }

    # ------------------------------------------------------------------
    def _write_tissue(self, drive):
        dna = self.dna
        rate = dna.mode_rate
        if rate <= 0.0 or not self.tissue_enabled:
            return
        n = len(drive)
        e = [math.tanh(d) ** 2 for d in drive]
        total = 0.0
        for v in e:
            total += v
        if total <= 0.0:
            return
        brate = dna.mode_baseline_rate
        z = self.tissue
        b = self.tissue_baseline
        for i in range(n):
            dev = e[i] / total - b[i]
            z[i] += rate * dev
            b[i] += brate * dev

    # ------------------------------------------------------------------

    # ------------------------------------------------------------------
    def tissue_profile(self):
        return [1.0 + self.dna.mode_amp * math.tanh(v) for v in self.tissue]

    def tissue_norm(self) -> float:
        return math.sqrt(sum(v * v for v in self.tissue))

    def reset_activity_state(self):
        n = self.dna.state_size
        self.state = [0.0] * n
        self.change_baseline = 0.0
        self.last_delta = 0.0
        self.last_drive = [0.0] * n
        self.age = 0
        return self

    def clone(self):
        other = LifeTissue(self.dna, self.inlet)
        other.state = list(self.state)
        other.change_baseline = self.change_baseline
        other.last_delta = self.last_delta
        other.last_drive = list(self.last_drive)
        other.age = self.age
        other.tissue = list(self.tissue)
        other.tissue_baseline = list(self.tissue_baseline)
        other.tissue_enabled = self.tissue_enabled
        return other
