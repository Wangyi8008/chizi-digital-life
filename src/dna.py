# -*- coding: utf-8 -*-

import math
import random

__all__ = ["LifeDNA", "Life"]


class LifeDNA:
    def __init__(
        self,
        dna_seed: int = 20260912,
        state_size: int = 64,
        channel_count: int = 6,
        eta: float = 0.05,
        gamma: float = 0.2,
        kappa: float = 0.6,
        neighborhood_sigma: float = 4.0,
        kernel_radius: int = 12,
        baseline_rate: float = 0.02,
    ):
        if state_size < 2:
            raise ValueError("state_size must be >= 2")
        if channel_count < 1:
            raise ValueError("channel_count must be >= 1")
        if not (0.0 < eta <= 1.0):
            raise ValueError("eta must be in (0, 1]")
        if not (0.0 < gamma <= 1.0):
            raise ValueError("gamma must be in (0, 1]")
        if not (0.0 <= kappa):
            raise ValueError("kappa must be >= 0")
        if not (0.0 < baseline_rate <= 1.0):
            raise ValueError("baseline_rate must be in (0, 1]")

        self.dna_seed = int(dna_seed)
        self.state_size = int(state_size)
        self.channel_count = int(channel_count)
        self.eta = float(eta)
        self.gamma = float(gamma)
        self.kappa = float(kappa)
        self.neighborhood_sigma = float(neighborhood_sigma)
        self.kernel_radius = int(kernel_radius)
        self.baseline_rate = float(baseline_rate)

        rng = random.Random(self.dna_seed)
        entry_scale = 1.0 / math.sqrt(self.channel_count)
        self.entry_weights = [
            [rng.gauss(0.0, entry_scale) for _ in range(self.channel_count)]
            for _ in range(self.state_size)
        ]

        radius = min(self.kernel_radius, self.state_size // 2)
        raw = []
        total = 0.0
        for off in range(-radius, radius + 1):
            w = math.exp(-(off * off) / (2.0 * self.neighborhood_sigma ** 2))
            raw.append((off, w))
            total += w
        self._kernel_offsets = [(off, w / total) for off, w in raw]

    # ------------------------------------------------------------------
    def internal_coupling(self, s):
        n = len(s)
        local = [0.0] * n
        offsets = self._kernel_offsets
        for i in range(n):
            acc = 0.0
            for off, w in offsets:
                acc += w * s[(i + off) % n]
            local[i] = acc
        return [local[i] - s[i] for i in range(n)]

    def internal_coupling_spectrum(self):
        n = self.state_size
        spectrum = []
        for k in range(n):
            s = 0.0
            for off, w in self._kernel_offsets:
                s += w * math.cos(2.0 * math.pi * k * off / n)
            spectrum.append(s - 1.0)
        return spectrum

    def expected_retention_range(self):
        spec = self.internal_coupling_spectrum()
        factors = [1.0 + self.eta * (self.kappa * lam - self.gamma) for lam in spec]
        return min(factors), max(factors)

    def entry_drive(self, r):
        n = len(self.entry_weights)
        d = self.channel_count
        out = [0.0] * n
        for i in range(n):
            row = self.entry_weights[i]
            acc = 0.0
            for k in range(d):
                acc += row[k] * r[k]
            out[i] = acc
        return out

    def describe(self) -> str:
        return (
            "DNA(seed=%d, N=%d, D=%d, eta=%g, gamma=%g, kappa=%g, sigma=%g, radius=%d, mu=%g)"
            % (
                self.dna_seed,
                self.state_size,
                self.channel_count,
                self.eta,
                self.gamma,
                self.kappa,
                self.neighborhood_sigma,
                self.kernel_radius,
                self.baseline_rate,
            )
        )

class Life:
    def __init__(self, dna: LifeDNA, inlet):
        if dna.channel_count != inlet.channel_count:
            raise ValueError("DNA channel count does not match the physical carrier")
        self.dna = dna
        self.inlet = inlet
        self.state = [0.0] * dna.state_size

        self.change_baseline = 0.0
        self.last_delta = 0.0
        self.last_drive = [0.0] * dna.state_size
        self.age = 0

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

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = real_drive[i] + kappa * internal_drive[i]
            drive_out[i] = drive
            new_state[i] = s[i] + eta * (math.tanh(drive) - gamma * s[i])

        acc = 0.0
        for i in range(n):
            diff = new_state[i] - s[i]
            acc += diff * diff
        delta = math.sqrt(acc)

        self.state = new_state
        self.last_drive = drive_out
        self.last_delta = delta
        self.change_baseline = (
            (1.0 - dna.baseline_rate) * self.change_baseline
            + dna.baseline_rate * delta
        )
        self.age += 1
        return {
            "tick": self.age,
            "delta": delta,
            "baseline": self.change_baseline,
            "same_or_different": delta - self.change_baseline,
        }

    # ------------------------------------------------------------------

    # ------------------------------------------------------------------
    def state_size(self) -> int:
        return len(self.state)

    def state_norm(self) -> float:
        return math.sqrt(sum(v * v for v in self.state))

    def snapshot(self):
        return list(self.state)

    def clone(self):
        other = Life(self.dna, self.inlet)
        other.state = list(self.state)
        other.change_baseline = self.change_baseline
        other.last_delta = self.last_delta
        other.last_drive = list(self.last_drive)
        other.age = self.age
        return other

    def adopt_state(self, other):
        if len(other.state) != self.state_size():
            raise ValueError("state size mismatch")
        self.state = list(other.state)
        self.change_baseline = other.change_baseline
        self.last_delta = other.last_delta
        self.age = other.age
        return self

    def runtime_slots(self):
        slots = []
        for name, value in sorted(vars(self).items()):
            if isinstance(value, list):
                slots.append((name, len(value)))
            elif isinstance(value, (int, float)):
                slots.append((name, 1))
        return slots
