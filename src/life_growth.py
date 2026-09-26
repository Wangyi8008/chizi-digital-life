# -*- coding: utf-8 -*-
"""The formal Life: one file, one class.

What this file is
    This is the only Life implementation.  Every mechanism that still stands
    is written here once, in the order it really runs in.  `LifeGrowth` below
    plus `src/dna.py`, `src/life_tissue.py` and `src/inlet.py` are the whole
    of it, and no other file has to be read to know what runs.

    The mechanisms:

        the trunk             the growing state, the tissue, the traces, the
                              relation memory and its recall, the innate
                              addressing, the way out
        the base              the material a moment is read out of: which
                              changes go together, what their ends are, and
                              what those ends' organisation is.  It is worked
                              through in that order because that is how it is
                              computed, and that order is not what the Life
                              sees -- what the Life sees is LAS, below, which
                              shows the whole of it at once
        the three states      stable / mismatch / broken, judged off the
                              Connection itself and the Structure it was really
                              formed in: whether it still holds, and whether
                              that Structure's own organisation still stands
        LAS                   showing the real structure that is there now
        MSIU                  forming, out of what is still really acting, the
                              organisation a mismatched or broken Connection
                              is answered with
        the history           a Structure is kept with its own identity, and a
                              real run of it can be brought back as an end
        the ownership         which end belongs to which whole, and through
                              which port
        the form lane         a language form that really arrives takes part
                              in this very moment, with a place and a presence
        the one list          what this moment is carrying, and nothing else

What is deliberately not claimed
    Not that a moment is ever free: reality's channels and the behaviour ends
    are there every moment, so the connection judgement never walks fewer than
    twelve ordered pairs' worth of ends.  Not that knowledge makes thinking
    faster.  Only that the history may grow while a moment pays for what is
    really taking part in it.

How the state file is written
    One file, in two parts: the manifest, which is the payload with every long
    run of floats replaced by where its values lie, and the values themselves,
    raw little-endian float64.  Nothing is rounded, dropped, averaged or
    merged; the same payload written that way takes a little over a third of
    the room the JSON text took.  It is read once for the whole load, not once
    for every layer of the chain the load passes through.  Reading it back puts
    the identities and what they have formed back, and stands this moment's own
    tables up empty beside them, so an Element that came back can take part
    again instead of being assumed never to have been (`_align_now`).

Switches
    Each one is behind its own switch, defaulting to the corrected behaviour;
    setting the switch to False gives the other behaviour back,
    value for value.

    `one_reality_per_moment_enabled` (default True)
        External information enters once.  The moment after it is the Life's
        own activity continuing inside consciousness; the passes that read
        reality are not handed the same external frame again.
    `expression_experiences_enabled` (default True)
        The organ keeps the experiences it really had with a form, not one
        averaged vector per form, and chooses among what it really met.  One
        form is not one vector, and one expression does not have one fixed
        form.
    `las_scope_enabled` (default True)
        LAS is a step this Life really runs: once a moment it shows the real
        structure that is there, and MSIU forms its answer out of that showing
        instead of reading the structure again.
    `history_enabled` (default True)
        dump / load carry the history of the formed Connection / Element /
        Structure / run: their identities and their organisation.  What they
        do not carry is the current running: which of them is acting now, and
        the current three states, are formed again from what really happens
        next.  The scales this Life has itself read out of its own experience,
        and which cannot be read again out of that history, travel with it.
    `self_ref_scale_enabled` (default True)
        The scales that decide are this Life's own.  How strongly a relation
        must hold before it is acting, whether some ends are one Element,
        whether an organisation is a Structure, which of the three states a
        Connection is in, and whether an experience continues one of its
        relations, are read off what this Life has already formed -- its own
        Connections and their own best readings, its own Elements, its own
        Structures and how long they have run -- and not off a number that is
        the same for every Life.  What is left fixed is only the reach and the
        resolution of the reading itself: how far back the change now is
        compared with the change then, over how many moments the fit is taken,
        and how much must have been seen before a fit is read at all.  Off,
        every judgement is the constant's own, value for value.
    `whole_level_enabled` (default True)
        A formed Structure that is taking part stands at the level above as
        **one** participant: its own place is what stands in the group's member
        table, and what is inside it stays inside it -- not copied, not renamed,
        not flattened out beside the bigger organisation it is standing in.  So
        a larger organisation has an Element that is a Structure, and the
        recursion is really a recursion rather than a wider flat piece.  Only a
        Structure that really ran on the moment is taken up this way, and where
        several cover a unit the outermost one covers it.
    `st_identity_enabled` (default True)
        A formed Structure is running again as soon as the organisation it was
        born with stands **whole** inside what is acting now -- every one of its
        own members and every one of its own inner Connections still there.  What
        the piece has grown beyond that is the larger reality the Structure is
        standing in, and is not part of its identity.  This is what lets a
        Structure go on running under its own identity while a larger
        organisation stands inside it, and it is the other half of what
        `whole_level_enabled` needs: a Structure's own place can only become an
        end of a Connection if it is carried while the Structure runs.
"""

import array
import bisect
import io
import json
import math
import os
import random
import struct
import sys
from collections import deque
import hashlib
from operator import mul as _mul

from src.dna import Life, LifeDNA
from src.life_tissue import LifeDNA04, LifeTissue
from src.inlet import RealityInlet

# --- constants
ADDR_BITS = 10
ADDR_BUCKETS = 1024
ADDR_TABLES = 6
BEHAVIOR_CHANNELS = 6
BROKEN = 2
# Round 67.  Which of the scales below are still the Life's own ability, and
# which are only what its own history stands in for while
# `self_ref_scale_enabled` is off.
#
# Kept, because they say nothing about any particular world: the reach of the
# reading and its resolution.  How far back the change now is compared with the
# change then, over how many moments the fit is taken, and how many moments
# must have been seen before a fit is read at all -- these bound what can be
# perceived, not what is there.
CH_LAG = 20
CH_MIN = 150
CH_WINDOW = 200
# Off only.  On, what stands in its place is `_own_conn_bar`: the average of the
# best reading each of this Life's own Connections has reached.
CH_R2_MIN = 0.15
DNA_TUPLE_FIELDS = ['_kernel_offsets']
# Off only.  On, whether some ends are one Element is read off the Elements this
# Life already has: the one standing whole inside what acts now (`_own_merge`),
# and two units are grouped when one's own support stands whole inside the
# other's (`_own_group`).
END_JACCARD = 0.5
END_MERGE = 0.5
EXPRESSION_SECTION = 'expression'
FORM_MARGIN = 0.05
LIFE = 'life'
LIFE_FIELDS_11 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
LIFE_FIELDS_12 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
LIFE_FIELDS_13 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
LIFE_FIELDS_14 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
LIFE_FIELDS_15 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
LIFE_FIELDS_16 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
LIFE_FIELDS_17 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
LIFE_FIELDS_18 = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled', 'experience_flow']
# What the memory layer writes as itself.  Its relations are the Connections,
# so everything per-relation goes with the history (see `_history_of`); what is
# left here is the switch and the running mean of change the continuity is read
# against -- the substrate, and nothing else.
MEMORY_FIELDS = ['memory_enabled', 'bar_d']
# Off only.  On, recognition is judged against the matches this Life has itself
# read: an experience continues a relation when it stands at least as close to
# it as the experiences it has already had stood to theirs (`_own_theta`).
MEM_THETA = 0.97
MISMATCH = 1
MSIU_KIND_WORDS = {'repair': 'the whole again, out of the pieces that still act', 'rebuild': 'a smaller organisation, out of what is left'}
MSIU_KIND_NAMES = {'repair': 'mismatched', 'rebuild': 'broken'}
OUT_SEED_OFFSET = 90210
# Names a Life must not carry over when one Life is made out of another: the
# symbol layer's own names, which are no longer kept, and the moment's own
# view of the recall.
RETIRED_FIELDS = ['mem_active_fired', 'mem_active_touched', 'mem_active_computed', 'mem_active_fireable', 'mem_active_set', 'mem_fired_last', 'mem_g_last', 'mem_coeff', 'mem_last_u', '_mem_part_last']
# Off only.  On, the three states are read off the Connection itself and the
# Structure it was really formed in (`_own_state`): broken when the Connection
# no longer holds -- its own reading fallen past the weakest share this Life has
# held one of its own relations at while it still held (`_own_break_share`) --
# and mismatch when it does still hold and yet can no longer match that
# Structure's own organisation, either because that organisation does not stand
# again (`_st_standing_now`) or because the Connection is running against the
# very way that organisation gave it, by as much as the least definite manner
# this Life has formed one at (`_own_dir_floor`).
SF_BROKEN_SHARE = 0.25
SF_DIR_EPS = 0.1
SOURCE_DIM = 2
SOURCE_TAG = b'P7_interaction_01|language-source-physical-connections|v1'
STABLE = 0
STATE_NAMES = {0: 'stable', 1: 'mismatch', 2: 'broken'}
# Off only.  On, how long an organisation must stand before it is a Structure is
# read off how long this Life's own Structures have run, capped at the reading's
# own resolution `CH_MIN` (`_own_st_bar`), and a piece that already holds one of
# them whole carries that one's own run over (`_st_run_inside`).
ST_MIN = 100
TRACE_FIELDS = ['trace_keys', 'trace_cont', 'trace_born', 'trace_used', 'last_trace_age', 'trace_enabled', 'trace_formation_enabled', 'trace_shaping_enabled', 'trace_injection_on', 'last_trace_g', 'last_trace_w', 'last_trace_in', 'last_trace_fired']
V07_FIELDS = ['state', 'tissue', 'tissue_baseline', 'latent_activity', 'coupling', 'change_baseline', 'last_delta', 'last_drive', 'age', 'growth_enabled', 'tissue_enabled']
VOICE_CH = 0
VOICE_NO = '\u4e59'
VOICE_YES = '\u7532'
WORDS = ('\u7532', '\u4e59')
WORD_KIND = 'f'
ZERO = 0.0
EXPERIENCE_KEEP = 64   # how many meetings one form keeps
HISTORY_SECTION = "history"

# --- the state file's own shape
#
# One file, and in it two parts: the manifest, which is the same payload the
# JSON file held, and beside it the float64 values themselves.  Every run of
# floats long enough to matter is written as eight raw bytes per value instead
# of as a decimal string, and the manifest holds only where it lies.  Nothing
# is rounded, averaged, merged or dropped: the same numbers, the same order,
# the same tables, and a file a little over a third the size.
STATE_MAGIC = b"LIFEBIN1"
STATE_BLOCK_MIN = 64   # a shorter run of floats is not worth a block


def _rest(d, keys):
    """The keywords a call did not name itself, passed on as they came."""
    return dict((k, v) for k, v in d.items() if k not in keys)

# --- helper functions

def _dot(u, v):
    return sum(u[i] * v[i] for i in range(len(u)))

def _shape(v):
    n = len(v)
    bar = sum(v) / n
    d = [x - bar for x in v]
    r = math.sqrt(sum(x * x for x in d))
    if r <= 1e-12:
        return None
    return [x / r for x in d]

def _addressed_touch(self, s):
    """What this Life brings back, out of the relations it has really formed.

    The memory keeps no relations of its own.  A relation is a Connection, and
    every row here stands beside one, in the Connection's own id: how much it is
    in play, the moments it was really continued, and the experience it came
    about in.  So a recall comes back as this Life's own Connections -- their
    own ends, moved the way their own first acting said they move -- and nothing
    comes back that this Life has not formed.

    What stays here and forms nothing is the continuity: `bar_d`, `mem_prev_u`
    and `mem_inj_prev` carry the moment before's experience into this one, and
    that is all they do.
    """
    if not self.memory_enabled:
        w0 = [0.0] * len(self.trace_keys)
        g0 = [0.0] * len(self.trace_keys)
        self.last_trace_g, self.last_trace_w = g0, w0
        self.last_trace_in, self.last_trace_fired = [0.0] * len(s), 0
        return [0.0] * len(s), w0, g0

    n = len(s)
    d_real = list(self.last_d_reality) if self._mem_have_input else None
    # Inside consciousness there is no new reality, but the internal activity
    # itself keeps changing the current state. That internal change is a real
    # change of the Life as well, so it is what the experience continues from.
    d_now = d_real
    if d_now is None and self.conscious_active and self.conscious_ticks > 0:
        di = self.last_conscious_d_internal
        d_now = list(di) if di is not None else None
    inj_prev = self.mem_inj_prev if self.mem_inj_prev is not None else [0.0] * n

    # The entry is the Life's own continuous experience: what the current
    # internal state already carries, plus the change this moment caused,
    # plus what the previous step recalled, with the running common
    # component of experience removed.  This is the substrate, and the only
    # thing here that is not read off a Connection.
    src = [s[i] + inj_prev[i] for i in range(n)]
    if d_now is not None:
        bar = self.bar_d
        for i in range(n):
            src[i] += d_now[i] - bar[i]
    u = _shape(src)
    self.mem_last_u = u

    # --- the relations this Life is at -----------------------------------
    # A relation carries activation while it is really in play, and activation
    # also travels along the ends the Connections really share, one relation-hop
    # per moment, losing per hop exactly what an unused participation loses per
    # moment.  A relation that has gone quiet is therefore still reachable for
    # as long as it is still connected to what the current Life is doing,
    # however much time has passed.  Nothing outside that reach is looked at,
    # and there is no look-up over the whole memory.
    cand = [k for k in self.mem_front if self._mem_act_now(k) >= self.mem_floor]
    self.mem_active_set = cand
    self.mem_active_touched = len(cand)

    # --- recognition: does this experience continue one of them? ----------
    best, bk = -2.0, -1
    if u is not None:
        for k in cand:
            kk = self.cn_key[k]
            g = _dot(u, kk) if kk is not None else 0.0
            if g > best:
                best, bk = g, k
    self.mem_g_last = [best]
    self.mem_active_computed = len(cand)
    self.mem_search_size = len(cand)

    # A relation is continued whenever there is a real change to continue from:
    # a moment of reality outside, or the internal change of the current
    # consciousness inside.  Nothing is formed here -- forming a relation is the
    # Connections' own work, and all this reads is which of them this experience
    # continues.
    if u is not None and d_now is not None:
        self.mem_frames += 1
        # the bar this moment is judged against is read before this moment's own
        # match goes in with the rest (`_own_theta`).  What it finds out here is
        # known from the next moment on and never counts against itself.
        theta = self._own_theta()
        if bk >= 0 and best >= theta:
            self.mem_recognized += 1
            self.mem_last_recognized = bk
            lam = self.mem_lam
            self.mem_s[bk] += lam * (1.0 - self.mem_s[bk])
            self.mem_hit[bk] += 1
            self._mem_part_now[bk] = 1.0
        if bk >= 0:
            # what that bar is read from: the matches this Life has itself read
            self.mem_g_sum = getattr(self, "mem_g_sum", 0.0) + best
            self.mem_g_n = getattr(self, "mem_g_n", 0) + 1

    # --- recall: this Life's own relations, brought back ------------------
    inj = [0.0] * n
    ww = {}
    fired = []
    key = u if u is not None else self.mem_prev_u
    cand_fire = [k for k in cand if self.mem_s[k] > 0.0]
    if self.address_enabled:
        # the internal long-term addressing entry.  The cue is the one the
        # recall already uses; the addresses come from the experience each
        # Connection came about in; the buckets hold only Connection ids.  Six
        # buckets are read and nothing is scanned.
        _hits = () if key is None else self._addr_lookup(key)
        self.addr_found = len(_hits)
        self.addr_not_local = 0
        self.addr_extra = 0
        self.addr_hits = ()
        _local = set(cand)
        _seen = set(cand_fire)
        _added = []
        for _k in _hits:
            if _k in _local:
                continue
            self.addr_not_local += 1
            if self.mem_s[_k] > 0.0 and _k not in _seen:
                _seen.add(_k)
                cand_fire.append(_k)
                _added.append(_k)
        self.addr_hits = tuple(_added)
        self.addr_extra = len(_added)
    self.mem_active_fireable = len(cand_fire)
    if key is not None and cand_fire:
        rs = {}
        top = -2.0
        for k in cand_fire:
            kk = self.cn_key[k]
            r = _dot(key, kk) if kk is not None else -2.0
            rs[k] = r
            if r > top:
                top = r
        for k, r in rs.items():
            if r < top - self.mem_margin or r <= 0.0:
                continue
            coeff = self.mem_s[k] * r
            ww[k] = coeff
            fired.append(k)
            if coeff > self._mem_part_now.get(k, 0.0):
                self._mem_part_now[k] = coeff
            # what comes back is the Connection itself: both ends it stands
            # between, moved the way its own first acting said they move.
            w = coeff * self.cn_way[k]
            x, y = self.cn_pre[k], self.cn_post[k]
            if 0 <= x < n:
                inj[x] += w
            if 0 <= y < n:
                inj[y] += w

    self.mem_coeff = ww
    self.mem_active_fired = len(fired)
    self.mem_fired_last = tuple(fired)
    ret_w = [0.0] * len(self.trace_keys)
    ret_g = [0.0] * len(self.trace_keys)
    self.last_trace_g = ret_g
    self.last_trace_w = ret_w
    self.last_trace_in = inj
    self.last_trace_fired = len(fired)

    if d_real is not None:
        rb = self.mem_rho
        for i in range(n):
            self.bar_d[i] = (1.0 - rb) * self.bar_d[i] + rb * d_real[i]
    if d_now is not None and u is not None:
        # The experience that just happened is the one the next experience
        # continues from, outside reality and inside consciousness alike.
        self.mem_prev_u = list(u)
    self.mem_inj_prev = list(inj)

    part = dict(self._mem_part_now)
    self._mem_apply_participation()
    # Activation then flows one relation-hop onward along the ends the
    # Connections really share, so it advances one real relation per moment and
    # cannot pour through the whole memory at once.
    flowed = self._mem_flow()
    self._mem_front_extend(part, flowed)
    return inj, ret_w, ret_g

def _cos(a, b):
    na, nb = _norm(a), _norm(b)
    if na <= 1e-18 or nb <= 1e-18:
        return 0.0
    return sum(a[i] * b[i] for i in range(len(a))) / (na * nb)

def _norm(v):
    return math.sqrt(sum(x * x for x in v))

def _plain(value):
    if isinstance(value, list):
        if value and isinstance(value[0], list):
            return [list(row) for row in value]
        return list(value)
    return value

def _plain_rows(value):
    if not isinstance(value, list):
        return value
    return [None if row is None else list(row) for row in value]

def _r2(win, m):
    """What the change now has to do with the change CH_LAG moments back.

    Read in two passes: the window's own mean comes first, and only what is
    left after subtracting it is squared.  That is the same number on paper as
    (sum of squares)/m - mean*mean, and it is not the same number in floating
    point.  When a side stops changing the window becomes a run of one value,
    and the one-pass form then takes the difference of two quantities that are
    nearly equal: what should be exactly zero comes out as rounding error, a
    few times 1e-17, which is above any guard that only tests for exact zero.
    The ratio built on two such numbers is arbitrary, and it was read as a
    relation -- measured, pairs whose last 200 changes were all zero came out at
    3.38 and 31.69, and were held as connections.  A window with nothing in it
    has nothing to account for.

    So: two passes, and one exact test.  If either side holds a single value
    across the whole window there is no change on that side at all, and the
    answer is 0 however the arithmetic happens to fall.
    """
    buf = win["buf"]
    sx = sy = 0.0
    first_x, first_y = buf[0]
    one_x = one_y = True
    for x, y in buf:
        sx += x
        sy += y
        if x != first_x:
            one_x = False
        if y != first_y:
            one_y = False
    if one_x or one_y:
        return 0.0, 0.0
    mx, my = sx / m, sy / m
    vx = vy = cv = 0.0
    for x, y in buf:
        dx, dy = x - mx, y - my
        vx += dx * dx
        vy += dy * dy
        cv += dx * dy
    vx, vy, cv = vx / m, vy / m, cv / m
    if vx <= 0.0 or vy <= 0.0:
        return 0.0, 0.0
    r = cv / math.sqrt(vx * vy)
    return r * r, r

def entry_rms(dna):
    vals = [w for row in dna.entry_weights for w in row]
    return math.sqrt(sum(v * v for v in vals) / len(vals))

def make_source_weights(dna, source_dim=SOURCE_DIM, tag=SOURCE_TAG):
    scale = entry_rms(dna)
    seed = int.from_bytes(
        hashlib.sha256(tag + b"|dna_seed=" + str(int(dna.dna_seed)).encode("ascii")).digest()[:8],
        "big")
    rng = random.Random(seed)
    n = dna.state_size
    weights = [[rng.gauss(0.0, scale) for _ in range(source_dim)] for _ in range(n)]
    return weights, scale, seed

# --- helpers of the small classes

def _is_zero(v):
    """Whether a value is the zero a place that is not taking part carries.

    `-0.0` is not that zero: it is a value a place really carries, and the base
    writes it down as what it is.  Only a positive zero says "nothing here".
    """
    return v == ZERO and math.copysign(1.0, v) > ZERO


class SourceEntryProxy:
    def __init__(self, dna, life):
        object.__setattr__(self, "_dna", dna)
        object.__setattr__(self, "_life", life)

    def entry_drive(self, r):
        base = self._dna.entry_drive(r)
        v = object.__getattribute__(self, "_life")._frame_source
        if v[0] == 0.0 and v[1] == 0.0:
            return list(base)
        W = object.__getattribute__(self, "_life").source_weights
        return [base[i] + W[i][0] * v[0] + W[i][1] * v[1] for i in range(len(base))]

    def __getattr__(self, name):
        return getattr(object.__getattribute__(self, "_dna"), name)

class StructureReadings(object):
    """The reality the higher board is fed: what each formed structure is doing.

    One channel per structure that has really formed, in the order they were
    given their identity.  The values are the readings this implementation takes
    for a structure; nothing else about a structure ever goes in, and nothing
    here says what a structure is or which ones belong together.
    """

    def __init__(self, channel_count=0):
        # The carrier check is made once, when the board is built, and a carrier
        # has to say how many channels it has.  There is one channel per formed
        # structure, so the number is whatever the lower board has formed by the
        # moment this carrier is built; it is kept in step with the board as
        # structures appear, and nothing else is read off it.
        self.channel_count = int(channel_count)
        self.values = []

    def frame(self, samples=None):
        return list(self.values)

    def silence(self):
        return []

    def describe(self) -> str:
        return ("StructureReadings()  # one channel per formed structure, "
                "carrying no semantics")

class Running(list):
    """The base's own count of the moments a Structure ran, noting its writes.

     counts a running moment in one place and one place only -- it adds one
    to that Structure's own entry of this table -- and nothing else in the base
    ever writes it.  So the table can say which of its entries really moved, and
    which of them rose, and that is the whole of this class: the same numbers,
    kept the same way, with the two questions noted as they are answered.  An
    entry set to what it already held is not a move and is not noted -- which is
    exactly the question  asked by comparing every entry against its own
    value before the moment, and the question  asked with `>`.
    """

    def __init__(self, seq=()):
        list.__init__(self, seq)
        self.moved = set()   # entries that changed on this moment
        self.rose = set()    # of those, the ones that went up

    def __setitem__(self, i, v):
        if not isinstance(i, int):
            list.__setitem__(self, i, v)
            return
        was = list.__getitem__(self, i)
        list.__setitem__(self, i, v)
        if v != was:
            self.moved.add(i)
            if v > was:
                self.rose.add(i)

class Growing(list):
    """A table whose entries are written once and then read for ever.

    `st_ends` and `el_ends` are written when a Structure or an element is made,
    and the ownership layer reads them every moment.  Whether that reading can
    be taken once has to be measured rather than believed, so the same list is
    kept here with the entries that were written noted; anything written after
    the reading was taken is read again.
    """

    def __init__(self, seq=()):
        list.__init__(self, seq)
        self.written = set()

    def __setitem__(self, i, v):
        if not isinstance(i, int):
            list.__setitem__(self, i, v)
            return
        list.__setitem__(self, i, v)
        self.written.add(i)

    def __delitem__(self, i):
        list.__delitem__(self, i)
        self.written.clear()

class Series(object):
    """One connection's own history of one quantity, as the stretches it ran.

    Read as a sequence of one entry per judged moment -- `len`, indexing,
    slicing, iteration, `count` and equality against a plain list all answer
    what the plain list answered -- but kept as the stretches: while the value
    does not change, nothing is written, and the last stretch simply lasts until
    the moment it is asked for.

    The length is not stored.  It is the number of moments the connection has
    been judged, which the Life behind it answers (`sf_pos`), so a series that
    has held one value for ten thousand moments costs one entry and nothing
    else.
    """

    __slots__ = ("life", "key", "val", "beg")

    def __init__(self, life, key):
        self.life = life
        self.key = key
        self.val = []      # the value of each stretch
        self.beg = []      # the judged position each stretch began at (1-based)

    # -- writing ---------------------------------------------------------
    def put(self, v, pos):
        """One judged moment, at position `pos`.  The same value is not written.

        What comes back says whether this moment began a new stretch -- the one
        question the base's own `_sf_changes` counter needs beside the state.
        """
        if self.val and self.val[-1] == v:
            return False           # the same value carried on: the stretch lasts
        self.val.append(v)
        self.beg.append(pos)
        return True

    def seed(self, values):
        """Take a plain history that was lived before this implementation was on."""
        for i, v in enumerate(values):
            self.put(v, i + 1)

    def stretches(self):
        return len(self.val)

    # -- reading ---------------------------------------------------------
    def __len__(self):
        return self.life.sf_pos(self.key)

    def at(self, pos):
        """The value this series held at judged position `pos` (1-based)."""
        i = bisect.bisect_right(self.beg, pos) - 1
        if i < 0:
            i = 0
        return self.val[i]

    def __getitem__(self, i):
        n = len(self)
        if isinstance(i, slice):
            return [self.at(p) for p in range(*i.indices(n))]
        if i < 0:
            i += n
        if i < 0 or i >= n:
            raise IndexError("connection %r has been judged %d moment(s); "
                             "position %r is outside" % (self.key, n, i))
        return self.at(i + 1)

    def __iter__(self):
        n = len(self)
        beg = self.beg
        val = self.val
        if not val:
            return
        i = 0
        for p in range(1, n + 1):
            while i + 1 < len(beg) and beg[i + 1] <= p:
                i += 1
            yield val[i]

    def count(self, v):
        """How many judged moments held this value -- the stretches, added up."""
        n = len(self)
        beg = self.beg
        total = 0
        for i, x in enumerate(self.val):
            if x != v:
                continue
            end = (beg[i + 1] - 1) if i + 1 < len(beg) else n
            total += end - beg[i] + 1
        return total

    def __eq__(self, other):
        if isinstance(other, Series):
            return list(self) == list(other)
        if isinstance(other, (list, tuple)):
            return list(self) == list(other)
        return NotImplemented

    __hash__ = None

    def __repr__(self):
        return "<%d stretch(es) over %d judged moment(s)%s>" % (
            len(self.val), len(self), "" if len(self.val) <= 4
            else " " + repr(self.val[:3])[:-1] + ", ...]")

class Frames(dict):
    """The moments each connection has been judged in each of the three states.

    Read exactly as the base's own plain table is read -- `get`, indexing,
    membership, `items`, `keys`, iteration and `len` all answer what it
    answered -- but written only when a state ends.  What the stretch still
    going has added so far is added when the count is asked for, off the
    position the connection has reached: nothing is written for a state merely
    because it is still the state.

    It is a dictionary, because it is the table the base keeps, read the way the
    base reads it; what it holds is the stretches that have ended, and the
    stretch still going is answered from the position.
    """

    def __init__(self, life, closed=None):
        dict.__init__(self, closed or {})
        self.life = life

    # -- reading ---------------------------------------------------------
    def _open_of(self, key):
        """The stretch still going for this (connection, state), if it is this one."""
        if type(key) is not tuple or len(key) != 2:
            return None
        o = self.life.walk_sf_open.get(key[0])
        if o is None or o[0] != key[1]:
            return None
        return self.life.sf_pos(key[0]) - o[1] + 1

    def get(self, key, dflt=None):
        c = dict.get(self, key, 0)
        o = self._open_of(key)
        if o:
            c += o
        return c if c else dflt

    def __contains__(self, key):
        return self.get(key, 0) > 0

    def __getitem__(self, key):
        v = self.get(key, 0)
        if not v:
            raise KeyError(key)
        return v

    def __setitem__(self, key, v):
        dict.__setitem__(self, key, v)

    def _all(self):
        out = dict(dict.items(self))
        for k, (st, at) in self.life.walk_sf_open.items():
            got = out.get((k, st), 0) + self.life.sf_pos(k) - at + 1
            if got:
                out[(k, st)] = got
        return out

    def items(self):
        return list(self._all().items())

    def keys(self):
        return list(self._all().keys())

    def values(self):
        return list(self._all().values())

    def __iter__(self):
        return iter(self._all())

    def __len__(self):
        return len(self._all())

    def __eq__(self, other):
        if isinstance(other, Frames):
            return self._all() == other._all()
        if isinstance(other, dict):
            return self._all() == other
        return NotImplemented

    __hash__ = None

    def __repr__(self):
        return "<%d (connection, state) pair(s) held, %d still going>" % (
            dict.__len__(self), len(self.life.walk_sf_open))

class Carry(object):
    """The one list a moment is handed: what is taking part, and what it holds.

    Read exactly as the dense list was read -- `len`, indexing, iteration and
    `list()` all answer what the dense list answered -- but only the addresses
    that are taking part are held.  The width is the permanent address space, so
    every address the Life has ever made is answerable; one that is not taking
    part answers `0.0` and is not allocated, copied or walked.

    The width is never smaller than it was: a Structure or a run that has been
    given a place keeps it.  `grow` is the only thing that widens it, and it is
    called where the base made room.
    """

    __slots__ = ("_n", "_val")

    def __init__(self, n=0, val=None):
        self._n = int(n)
        self._val = dict(val) if val else {}

    # -- the permanent address space -------------------------------------
    def __len__(self):
        return self._n

    @property
    def width(self):
        """How many permanent addresses there are, as `participants()` says."""
        return self._n

    def grow(self, n):
        """Widen to the permanent address space, giving up no address."""
        n = int(n)
        if n < self._n:
            self._val = dict((u, v) for u, v in self._val.items() if u < n)
        self._n = n

    # -- what it carries -------------------------------------------------
    def __getitem__(self, u):
        if isinstance(u, slice):
            return self.as_list()[u]
        return self._val.get(u, ZERO)

    def __setitem__(self, u, v):
        if _is_zero(v):
            self._val.pop(u, None)
        else:
            self._val[u] = v

    def __contains__(self, u):
        return u in self._val

    def __iter__(self):
        """The same sequence the dense list gave, in address order."""
        return iter(self.as_list())

    def carried(self):
        """The addresses this moment is carrying, and their values."""
        return self._val

    def taking(self):
        """The addresses carrying something that is not zero, in address order.

        This is the base's own `[u for u in range(n) if frame_now[u] != 0.0]`,
        read off what is carried instead of off every address there is.
        """
        v = self._val
        return sorted(u for u in v if v[u] != ZERO)

    def as_list(self):
        """The whole permanent address space, as the dense list held it."""
        out = [ZERO] * self._n
        for u, v in self._val.items():
            if 0 <= u < self._n:
                out[u] = v
        return out

    def clear(self):
        self._val = {}

    def take(self, seq):
        """The frame this moment was handed: its values, where they stand.

        A place carrying exactly zero is the same thing as a place that is not
        carrying anything, and is not kept.
        """
        self._val = {}
        for i, x in enumerate(seq):
            v = float(x)
            if not _is_zero(v):
                self._val[i] = v

    def placing(self):
        """How many addresses the moment is carrying, zero ones left out."""
        return sum(1 for v in self._val.values() if v != ZERO)

    def __repr__(self):
        return "<%d address(es), %d carrying something>" % (
            self._n, self.placing())

# --- DNA: every field  in one class
class LifeDNA(LifeDNA04):
    # ---- __init__
    def __init__(self, source_dim: int = SOURCE_DIM, **kwargs):
        self.___init___step1(**kwargs)
        if source_dim < 1:
            raise ValueError("source_dim must be >= 1")
        self.source_dim = int(source_dim)
        self.source_weights, self.source_scale, self.source_seed = \
            make_source_weights(self, self.source_dim)

    # ---- ___init___step1
    def ___init___step1(self, latent_count: int = 64, latent_rate: float = 0.03,
                 growth_rate: float = 0.0005, injection: float = 0.3,
                 mode_rate: float = 0.002,
                 trace_count: int = 8, trace_gain: float = 0.1, trace_rate: float = 0.02,
                 trace_key_rate: float = 0.0005,
                 trace_margin: float = 0.05, trace_form_match: float = 0.35,
                 trace_refractory: int = 200, **kwargs):
        self.___init___step2(latent_count=latent_count, latent_rate=latent_rate,
                         growth_rate=growth_rate, injection=injection,
                         mode_rate=mode_rate, **kwargs)
        if trace_count < 0:
            raise ValueError("trace_count must be >= 0")
        if not (0.0 <= trace_rate <= 1.0):
            raise ValueError("trace_rate must be in [0, 1]")
        if not (0.0 <= trace_key_rate <= 1.0):
            raise ValueError("trace_key_rate must be in [0, 1]")
        if trace_gain < 0.0:
            raise ValueError("trace_gain must be >= 0")
        self.trace_count = int(trace_count)
        self.trace_gain = float(trace_gain)
        self.trace_rate = float(trace_rate)
        self.trace_key_rate = float(trace_key_rate)
        self.trace_margin = float(trace_margin)
        self.trace_form_match = float(trace_form_match)
        self.trace_refractory = int(trace_refractory)

    # ---- ___init___step2
    def ___init___step2(self, latent_count: int = 64, latent_rate: float = 0.03,
                 growth_rate: float = 0.0005, injection: float = 0.3,
                 mode_rate: float = 0.002, **kwargs):
        self.___init___step3(mode_rate=mode_rate, **kwargs)
        if latent_count < 1:
            raise ValueError("latent_count must be >= 1")
        if not (0.0 < latent_rate <= 1.0):
            raise ValueError("latent_rate must be in (0, 1]")
        if not (0.0 <= growth_rate <= 1.0):
            raise ValueError("growth_rate must be in [0, 1]")
        if injection < 0.0:
            raise ValueError("injection must be >= 0")
        self.latent_count = int(latent_count)
        self.latent_rate = float(latent_rate)
        self.growth_rate = float(growth_rate)
        self.injection = float(injection)

        rng = random.Random(self.dna_seed + 977)
        scale = 1.0 / math.sqrt(self.channel_count)
        self.latent_entry = [[rng.gauss(0.0, scale) for _ in range(self.channel_count)]
                             for _ in range(self.latent_count)]

    # ---- ___init___step3
    def ___init___step3(self, mode_amp: float = 0.6, mode_rate: float = 0.0,
                 mode_baseline_ratio: float = 50.0, **kwargs):
        self.___init___step4(**kwargs)
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

    # ---- ___init___step4
    def ___init___step4(
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
    **extra
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

    # ---- describe
    def describe(self) -> str:
        return self._describe_step1() + \
            "; everything the Life has formed is kept with it, and a moment does " \
            "not pay for how much of it there is"

    # ---- _describe_step1
    def _describe_step1(self) -> str:
        return self._describe_step2() + \
            "; the judgement keeps to the ends taking part now"

    # ---- _describe_step2
    def _describe_step2(self) -> str:
        return self._describe_step3() + \
            "; the whole Life acts, and an answered Structure joins in"

    # ---- _describe_step3
    def _describe_step3(self) -> str:
        return self._describe_step4() + \
            "; what is running now is what takes part"

    # ---- _describe_step4
    def _describe_step4(self) -> str:
        return self._describe_step5() + \
            "; every end is written where it really stands"

    # ---- _describe_step5
    def _describe_step5(self) -> str:
        return self._describe_step6() + \
            "; what the Life did is an end of its own, beside the reality"

    # ---- _describe_step6
    def _describe_step6(self) -> str:
        return self._describe_step7() + \
            "; the whole-of-relations layer a Life really formed runs again"

    # ---- _describe_step7
    def _describe_step7(self) -> str:
        return self._describe_step8() + \
            "; the organ keeps what the Life is really letting out, " \
            "and reads a form out on the axis of its act"

    # ---- _describe_step8
    def _describe_step8(self) -> str:
        return self._describe_step9() + \
            "; a kept run can take part again, in a slot of its own"

    # ---- _describe_step9
    def _describe_step9(self) -> str:
        return self._describe_step10() + \
            "; a formed way remembers the run it was formed in"

    # ---- _describe_step10
    def _describe_step10(self) -> str:
        return self._describe_step11() + \
            "; a Structure keeps the moments it really ran"

    # ---- _describe_step11
    def _describe_step11(self) -> str:
        return self._describe_step12() + \
            "; the Life itself takes part, as one more participant"

    # ---- _describe_step12
    def _describe_step12(self) -> str:
        return self._describe_step13() + \
            "; what MSIU formed is where the action is read off"

    # ---- _describe_step13
    def _describe_step13(self) -> str:
        return self._describe_step14() + \
            "; a state is answered by a Structure being formed"

    # ---- _describe_step14
    def _describe_step14(self) -> str:
        return self._describe_step15() + \
            "; LAS is asked about the state, and shows the whole"

    # ---- _describe_step15
    def _describe_step15(self) -> str:
        return self._describe_step16() + \
            "; the state a connection is in, kept as a record"

    # ---- _describe_step16
    def _describe_step16(self) -> str:
        return self._describe_step17() + \
            "; a formed structure keeps taking part, in the one place"

    # ---- _describe_step17
    def _describe_step17(self) -> str:
        return self._describe_step18() + \
            "; the organ's own experience goes with the Life"

    # ---- _describe_step18
    def _describe_step18(self) -> str:
        return self._describe_step19() + \
            "; a physical way out, and an organ that has met forms"

    # ---- _describe_step19
    def _describe_step19(self) -> str:
        return self._describe_step20() + \
            "; LAS -- the current real structure, shown as it is"

    # ---- _describe_step20
    def _describe_step20(self) -> str:
        return self._describe_step21() + \
            "; stable / mismatch / broken, read off the connection's own run"

    # ---- _describe_step21
    def _describe_step21(self) -> str:
        return self._describe_step22() + \
            "; the base reads the carrier, and only when reality arrives"

    # ---- _describe_step22
    def _describe_step22(self) -> str:
        return self._describe_step23() + \
            "; a structure is the organisation of its connections"

    # ---- _describe_step23
    def _describe_step23(self) -> str:
        return self._describe_step24() + \
            "; connection first, elements as what the connections show"

    # ---- _describe_step24
    def _describe_step24(self) -> str:
        return self._describe_step25() + \
            "; innate long-term addressing, 6 x 10-bit, over the relations this " \
            "Life has formed"

    # ---- _describe_step25
    def _describe_step25(self) -> str:
        return self._describe_step26() + \
            "; structure -- a whole of elements, taken as a unit again"

    # ---- _describe_step26
    def _describe_step26(self) -> str:
        return self._describe_step27() + \
            "; experience-addressed relation memory, with no external symbol entry"

    # ---- _describe_step27
    def _describe_step27(self) -> str:
        return self._describe_step28() + \
            "; relation memory chain"

    # ---- _describe_step28
    def _describe_step28(self) -> str:
        return self._describe_step29() + \
            "; thought result: the same structure keeps running after " \
            "finish_thinking()"

    # ---- _describe_step29
    def _describe_step29(self) -> str:
        return self._describe_step30() + \
            "; trace re-injection in consciousness weighted by max(g, 0)"

    # ---- _describe_step30
    def _describe_step30(self) -> str:
        return self._describe_step31() + "; thinking: thought_coupling"

    # ---- _describe_step31
    def _describe_step31(self) -> str:
        return self._describe_step32() + "; consciousness: ongoing conscious activity"

    # ---- _describe_step32
    def _describe_step32(self) -> str:
        return self._describe_step33() + (
            "; %d language source links, scale=%g, seed=%d"
            % (self.source_dim, self.source_scale, self.source_seed))

    # ---- _describe_step33
    def _describe_step33(self) -> str:
        return self._describe_step34() + (
            "; the frame's causal order, d_reality against key and content, and " \
            "the experience flow")

    # ---- _describe_step34
    def _describe_step34(self) -> str:
        return self._describe_step35() + (
            "; trace(K=%d, gain=%g, rate=%g, key_rate=%g, margin=%g, form_match=%g, " \
            "refractory=%d)"
            % (self.trace_count, self.trace_gain, self.trace_rate, self.trace_key_rate,
               self.trace_margin, self.trace_form_match, self.trace_refractory))

    # ---- _describe_step35
    def _describe_step35(self) -> str:
        return self._describe_step36() + (
            "; growth(M=%d, latent_rate=%g, growth_rate=%g, injection=%g, " \
            "residual growth + one-way A)"
            % (self.latent_count, self.latent_rate, self.growth_rate, self.injection))

    # ---- _describe_step36
    def _describe_step36(self) -> str:
        return self._describe_step37() + (
            "; tissue(mode_amp=%g, mode_rate=%g, baseline_ratio=%g, N dims, born all zero)"
            % (self.mode_amp, self.mode_rate, self.mode_baseline_ratio))

    # ---- _describe_step37
    def _describe_step37(self) -> str:
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

    # ---- entry_drive
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

    # ---- expected_retention_range
    def expected_retention_range(self):
        spec = self.internal_coupling_spectrum()
        factors = [1.0 + self.eta * (self.kappa * lam - self.gamma) for lam in spec]
        return min(factors), max(factors)

    # ---- internal_coupling
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

    # ---- internal_coupling_spectrum
    def internal_coupling_spectrum(self):
        n = self.state_size
        spectrum = []
        for k in range(n):
            s = 0.0
            for off, w in self._kernel_offsets:
                s += w * math.cos(2.0 * math.pi * k * off / n)
            spectrum.append(s - 1.0)
        return spectrum

    # ---- source_drive
    def source_drive(self, v):
        w = self.source_weights
        return [w[i][0] * v[0] + w[i][1] * v[1] for i in range(len(w))]


class LifeGrowth(LifeTissue):
    """The one formal Life: every mechanism that still stands."""

    # ---- __init__
    def __init__(self, *a, **k):
        self.___init___step1(*a, **k)
        self._start_walks()

    # ---- ___init___step1
    def ___init___step1(self, *a, **k):
        self.___init___step2(*a, **k)
        self.sp_keep = False
        self.sp_say = []

    # ---- ___init___step2
    def ___init___step2(self, *a, **k):
        self.___init___step3(*a, **k)
        self.sp_kept = []        # (moment, element, the forms in what it holds)
        self.sp_now = []         # the elements formed on this very moment
        self.sp_sent = []        # (moment, the forms the mouth sent)
        self.sp_asked = 0        # moments the mouth was handed something to send
        self.sp_silent = 0       # moments it was handed nothing

    # ---- ___init___step3
    def ___init___step3(self, *a, **k):
        self.___init___step4(*a, **k)
        self.init_words()

    # ---- ___init___step4
    def ___init___step4(self, *a, **k):
        self.___init___step5(*a, **k)
        self.ow_ports = {}          # owner -> the ends it carries things out on
        self.ow_owner = {}          # end -> the owner it belongs to
        self.ow_el_seen = {}        # element -> {"owners": [...], "ports": [...]}
        self.ow_st_seen = {}        # structure -> {"owners": [...], "ports": [...]}
        self.ow_st_first = {}       # structure -> the moment it first stood
        self.ow_st_moments = {}     # structure -> moments the Life was in it
        self.ow_st_port_moments = {}  # (structure, port) -> moments it carried it
        self.ow_kept = 0            # moments the ownership was applied on
        # The six behaviour ends are the ports of this one participant.  This is
        # the whole of the addition: no value is made, and no end is added.
        self.ow_join(LIFE, list(self.behavior_ends()))

    # ---- ___init___step5
    def ___init___step5(self, *a, **k):
        self.___init___step6(*a, **k)
        self.cn_local_enabled = True   # this version's change, as a whole

    # ---- ___init___step6
    def ___init___step6(self, *a, **k):
        self.___init___step7(*a, **k)
        self.structure_joins_enabled = True   # this version's change, as a whole

    # ---- ___init___step7
    def ___init___step7(self, *a, **k):
        self.___init___step8(*a, **k)
        self.join_on = True      # this version's change, as a whole
        self.join_zero = True    # and: what is not taking part carries nothing
        self.el_now = []         # per identity: the members acting now
        self.el_at = {}          # unit -> the identity its acting group is in now
        self.cur_el = []         # element identities taking part this moment
        self.cur_st = []         # structure identities running this moment
        self.keep_log = False    # a reading of the moment, off unless asked for
        self.join_log = []

    # ---- ___init___step8
    def ___init___step8(self, dna, inlet, past_structure_enabled=True,
                 behavior_count=BEHAVIOR_CHANNELS, **rest):
        self.___init___step9(dna, inlet, past_structure_enabled=past_structure_enabled,
                         **rest)
        self.behavior_count = int(behavior_count)
        if self.behavior_count < 0:
            raise ValueError("behavior_count must not be negative")
        self.bh_now = [0.0] * self.behavior_count   # what those ends carry now
        self.bh_set_moments = 0                     # times the organ set them

    # ---- ___init___step9
    def ___init___step9(self, dna, inlet, past_structure_enabled=True, **rest):
        self.___init___step10(dna, inlet, **rest)
        self.past_structure_enabled = bool(past_structure_enabled)

    # ---- ___init___step10
    def ___init___step10(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True, msiu_las_view_enabled=True, msiu_enabled=True,
                 structure_action_enabled=True, self_perception_enabled=True,
                 run_history_enabled=True, sf_run_enabled=True,
                 past_run_enabled=True, past_run_all=False,
    **extra):
        self.___init___step11(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled,
                         msiu_view_enabled=msiu_view_enabled,
                         msiu_las_view_enabled=msiu_las_view_enabled,
                         msiu_enabled=msiu_enabled,
                         structure_action_enabled=structure_action_enabled,
                         self_perception_enabled=self_perception_enabled,
                         run_history_enabled=run_history_enabled,
                         sf_run_enabled=sf_run_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled", "msiu_view_enabled", "msiu_las_view_enabled", "msiu_enabled", "structure_action_enabled", "self_perception_enabled", "run_history_enabled", "sf_run_enabled",)))
        self.past_run_enabled = bool(past_run_enabled)
        self.past_run_all = bool(past_run_all)

        # ---- the one list, after the base units -------------------------
        # A slot is given once and never moves, so which unit stands for what
        # is kept rather than worked out from where it sits.
        self.unit_kind = []        # per slot: "s" a Structure, "r" a run
        self.unit_ref = []         # per slot: which Structure, or which run
        self.st_unit = []          # per Structure: its slot, or -1
        self.rn_unit = []          # per run: its slot, or -1

        # ---- what each run's slot is carrying ---------------------------
        self.rn_form = []          # per run: the reading it carries now
        self.rn_on = []            # per run: brought back now, or not
        self.rn_by = []            # per run: the connections that brought it
        self.rn_brought = []       # per run: moments it has been brought back
        self.rn_epi = []           # per run: the stretches it was brought back
        self.rn_epi_open = []      # per run: is such a stretch going now

        self.pr_moments = 0        # moments the slots were read for
        self.pr_skipped = 0        # moments the ability was off
        self.pr_slots_given = 0    # slots given to runs
        self.pr_first_back = -1    # the moment the first run was brought back
        self.pr_bringing = 0       # moments at least one run was brought back

    # ---- ___init___step11
    def ___init___step11(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True, msiu_las_view_enabled=True, msiu_enabled=True,
                 structure_action_enabled=True, self_perception_enabled=True,
                 run_history_enabled=True, sf_run_enabled=True,
    **extra):
        self.___init___step12(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled,
                         msiu_view_enabled=msiu_view_enabled,
                         msiu_las_view_enabled=msiu_las_view_enabled,
                         msiu_enabled=msiu_enabled,
                         structure_action_enabled=structure_action_enabled,
                         self_perception_enabled=self_perception_enabled,
                         run_history_enabled=run_history_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled", "msiu_view_enabled", "msiu_las_view_enabled", "msiu_enabled", "structure_action_enabled", "self_perception_enabled", "run_history_enabled",)))
        self.sf_run_enabled = bool(sf_run_enabled)

        # connection -> the run of the Structure it was formed in.  Written
        # once, at the moment the way itself is written, and never again.
        self.sf_run = {}
        self.sf_run_written = 0    # ways that were given the run they came from
        self.sf_run_openless = 0   # moments at which a way was written and no
                                   # run of its Structure was open at all: the
                                   # runs are not being kept, so there is
                                   # nothing to point at
        self.sf_run_midrun = 0     # of those given one, written into a run that
                                   # had already begun rather than a fresh one
        self.sf_run_moments = 0    # moments the pairing was read for
        self.sf_run_skipped = 0    # moments the ability was off

    # ---- ___init___step12
    def ___init___step12(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True, msiu_las_view_enabled=True, msiu_enabled=True,
                 structure_action_enabled=True, self_perception_enabled=True,
                 run_history_enabled=True,
    **extra):
        self.___init___step13(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled,
                         msiu_view_enabled=msiu_view_enabled,
                         msiu_las_view_enabled=msiu_las_view_enabled,
                         msiu_enabled=msiu_enabled,
                         structure_action_enabled=structure_action_enabled,
                         self_perception_enabled=self_perception_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled", "msiu_view_enabled", "msiu_las_view_enabled", "msiu_enabled", "structure_action_enabled", "self_perception_enabled",)))
        self.run_history_enabled = bool(run_history_enabled)

        # one run per Structure per stretch of moments it really ran
        self.st_run_epi = []      # per Structure: its runs, in the order made
        self.st_run_open = []     # per Structure: the run still going, or -1
        self.st_run_ord = []      # per Structure: how many runs it has had

        self.rn_struct = []       # per run: which Structure it belongs to
        self.rn_ord = []          # per run: that Structure's own ordinal
        self.rn_start = []        # per run: the moment it began
        self.rn_stop = []         # per run: the moment it stopped, or None

        self.rn_moments = 0       # moments the runs were read for
        self.rn_skipped = 0       # moments the ability was off

    # ---- ___init___step13
    def ___init___step13(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True, msiu_las_view_enabled=True, msiu_enabled=True,
                 structure_action_enabled=True, self_perception_enabled=True,
    **extra):
        self.___init___step14(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled,
                         msiu_view_enabled=msiu_view_enabled,
                         msiu_las_view_enabled=msiu_las_view_enabled,
                         msiu_enabled=msiu_enabled,
                         structure_action_enabled=structure_action_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled", "msiu_view_enabled", "msiu_las_view_enabled", "msiu_enabled", "structure_action_enabled",)))
        self.self_perception_enabled = bool(self_perception_enabled)

        # what the Life unit carries: the whole-reading, held from the moment
        # before, the way st_form is held for a Structure.  Only
        # _life_unit_form writes it, and only from tables that already exist.
        self.lf_form = 0.0
        self.lf_moments = 0        # moments the Life unit was carried
        self.lf_skipped = 0        # moments the ability was off

    # ---- ___init___step14
    def ___init___step14(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True, msiu_las_view_enabled=True, msiu_enabled=True,
                 structure_action_enabled=True,
    **extra):
        self.___init___step15(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled,
                         msiu_view_enabled=msiu_view_enabled,
                         msiu_las_view_enabled=msiu_las_view_enabled,
                         msiu_enabled=msiu_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled", "msiu_view_enabled", "msiu_las_view_enabled", "msiu_enabled",)))
        self.structure_action_enabled = bool(structure_action_enabled)

    # ---- ___init___step15
    def ___init___step15(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True, msiu_las_view_enabled=True, msiu_enabled=True,
    **extra):
        self.___init___step16(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled,
                         msiu_view_enabled=msiu_view_enabled,
                         msiu_las_view_enabled=msiu_las_view_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled", "msiu_view_enabled", "msiu_las_view_enabled",)))
        self.msiu_enabled = bool(msiu_enabled)

        # One record per Connection MSIU has acted on, in the order it first did.
        self.ms_index = {}          # Connection identity -> record index
        self.ms_conn = []           # the Connection it is answering
        self.ms_kind = []           # repair / rebuild
        self.ms_connection = []     # the connection that asked for the change
        self.ms_from_structure = []  # the Structure that Connection was formed in
        self.ms_born = []           # the moment MSIU first acted on it
        self.ms_first = []          # the Structure it formed then
        self.ms_first_new = []      # was that a Structure the base had not had
        self.ms_structure = []      # the Structure it forms for it now, or -1
        self.ms_current = []        # is that Connection still mismatched or broken
        self.ms_moments = []        # moments MSIU has acted on it
        self.ms_new_structures = []  # Structures MSIU has caused to come about
        self.ms_trail = []          # (moment, structure, new) when that changed
        self.ms_ends = []           # the ends that were still there
        self.ms_pieces = []         # the connections among them that still act
        self.ms_left_out = []       # ends still there, taking part in nothing

        self.msiu_moments = 0       # moments MSIU was walked
        self.msiu_acted = 0         # moments it acted on at least one Connection

    # ---- ___init___step16
    def ___init___step16(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True, msiu_las_view_enabled=True,
    **extra):
        self.___init___step17(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled,
                         msiu_view_enabled=msiu_view_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled", "msiu_view_enabled",)))
        self.msiu_las_view_enabled = bool(msiu_las_view_enabled)

    # ---- ___init___step17
    def ___init___step17(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
                 msiu_view_enabled=True,
    **extra):
        self.___init___step18(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled,
                         recursion_enabled=recursion_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled", "recursion_enabled",)))
        self.msiu_view_enabled = bool(msiu_view_enabled)

        # The Connections a state has been read for, in the order they came about.
        # state that was really there, kept the way the Structures are kept: the
        # record stays after the state goes.
        # The record is absorbed: the identity is the Connection's own,
        #  and MSIU's own record is `ms_*` -- see `_ms_desc` / `_msiu_asked`)

        self.msiu_read_moments = 0   # moments the states were read
        self.msiu_read_none = 0     # moments no connection had a state yet

    # ---- ___init___step18
    def ___init___step18(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True, recursion_enabled=True,
    **extra):
        self.___init___step19(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled",)))
        self.recursion_enabled = bool(recursion_enabled)

        # what every formed Structure is doing now: one slot each, held beside
        # the Structures themselves the way el_form is held for an Element.
        # It is the Structure's own to hold; only _structure_own_form writes it.
        self.st_form = []
        self.take_part_moments = 0    # moments the whole list was walked
        self.take_part_skipped = 0    # moments the added ability was off

    # ---- ___init___step19
    def ___init___step19(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True,
    **extra):
        self.___init___step20(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, las_enabled=las_enabled,
                         expression_enabled=expression_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled", "expression_enabled",)))

    # ---- ___init___step20
    def ___init___step20(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
                 expression_enabled=True,
    **extra):
        self.___init___step21(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled,
                         las_enabled=las_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled", "las_enabled",)))
        self.expression_enabled = bool(expression_enabled)

        # ---- the way out: innate, born with the Life, never learned ----------
        self.out_weights = self._born_out_weights()

        # ---- the expression organ's own after-state --------------------------
        # form -> [the action the Life itself was letting out, times met]
        self.expression_forms = {}
        self.expression_acts = {}      # form -> the acts it was really met with
        self.expression_first = {}     # form -> the order it was first met in
        self.expression_met = 0        # forms really met
        self.expression_expressed = 0  # times it was asked to let one out

    # ---- ___init___step21
    def ___init___step21(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True, las_enabled=True,
    **extra):
        self.___init___step22(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled,
                         state_enabled=state_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled", "state_enabled",)))
        self.las_enabled = bool(las_enabled)

    # ---- ___init___step22
    def ___init___step22(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True, state_enabled=True,
    **extra):
        self.___init___step23(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled",)))
        self.state_enabled = bool(state_enabled)

        # the way a connection was running when the structure it was formed in
        # first ran: connection -> the sign of its manner then, written once
        self.sf_way = {}
        self.sf_born_in = {}         # connection -> the structure it was formed in
        # the connection's own state now, and what it has been
        self.sf_state = {}          # connection -> the state it is in
        # what LAS showed this moment, shown once and kept nowhere else
        self.las_shown = {}         # the base display, this moment
        self.sf_frames = {}          # (connection, state) -> moments
        self.sf_hist = {}            # connection -> the state at each moment
        self.sf_live_hist = {}       # connection -> what it really did
        self.sf_form_hist = {}       # connection -> the manner it ran with
        self.sf_changes = 0          # times a connection really changed state
        self.sf_moments = 0          # moments at least one connection was judged
        self.sf_never = 0            # moments before any formed way existed

    # ---- ___init___step23
    def ___init___step23(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True,
    **extra):
        self.___init___step24(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled",)))
        self.cog_frame = None    # the carrier that really arrived, this moment
        self.cog_steps = 0       # moments the base was really fed
        self.cog_skipped = 0     # moments with no reality of their own

    # ---- ___init___step24
    def ___init___step24(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True,
    **extra):
        self.___init___step25(dna, inlet, memory_enabled=memory_enabled,
                         address_enabled=address_enabled,
                         cognition_enabled=cognition_enabled, **_rest(extra, ("memory_enabled", "address_enabled", "cognition_enabled",)))
        self.st_ids = []
        self.st_index = {}          # (ends, edges) -> identity
        self.st_pending = {}        # organisation -> moments it has run so far
        self.st_ends = []           # which ends take part
        self.st_edges = []          # which end acts on which
        self.st_born = []
        self.st_frames = []         # moments the organisation was really running
        self.st_called = -1
        self.st_now_edges = ()

    # ---- ___init___step25
    def ___init___step25(self, dna, inlet, memory_enabled=True, address_enabled=True,
                 cognition_enabled=True,
    **extra):
        self.___init___step26(dna, inlet, memory_enabled=memory_enabled,
                         structure_enabled=False,
                         address_enabled=address_enabled, **_rest(extra, ("memory_enabled", "structure_enabled", "address_enabled",)))
        self.cognition_enabled = bool(cognition_enabled)

        # ---- the bare channels, as they arrive -------------------------
        self.frame_now = None
        self.ch_prev = None
        self.ch_hist = deque(maxlen=CH_LAG + 1)
        self.ch_steps = 0

        # ---- connection: two channels that really act on one another ----
        self.cn_index = {}          # (before, after) -> identity
        self.cn_pre = []
        self.cn_post = []
        self.cn_born = []
        self.cn_live = []           # what it accounts for right now
        self.cn_peak = []
        self.cn_form = []           # the sign and size it is running with now
        self.cn_window = {}         # pair -> running sums over the window
        self.cn_now = {}            # pair -> what it accounts for right now
        self.cn_best = {}           # pair -> the most it ever accounted for
        self.cn_best_full = {}      # the same, once the window was full

        # ---- the memory's own row beside each connection -----------------
        # one row per Connection, in the Connection's own id: the experience it
        # came about in, the way it first acted, and the ends it stands between
        self.cn_key = []            # the experience it came about in, frozen
        self.cn_way = []            # the way it first acted: +1.0 or -1.0
        self.cn_at = {}             # an end -> the Connections standing on it

        # ---- what the connections show: the ends ------------------------
        self.el_ends = []           # what each end is made of
        self.el_sides = []          # which parts it has played: 0 acts, 1 is acted on
        self.el_born = []
        self.el_frames = []
        self.el_form = []           # the current reading of its own channels
        self.el_grew = 0            # times an end took in another channel
        self.el_issued = 0          # ends that were ever given an identity

    # ---- ___init___step26
    def ___init___step26(self, dna, inlet, memory_enabled=True, structure_enabled=True,
                 address_enabled=True,
    **extra):
        self.___init___step27(dna, inlet, memory_enabled=memory_enabled,
                         structure_enabled=structure_enabled, **_rest(extra, ("memory_enabled", "structure_enabled",)))
        self.address_enabled = bool(address_enabled)
        self.addr_dim = int(dna.state_size)
        self.addr_seed = int(getattr(dna, "dna_seed", 0))
        self.addr_planes = self._addr_make_planes()
        self.addr_buckets = [dict() for _ in range(ADDR_TABLES)]
        self.addr_entries = 0
        self.addr_builds = 0
        self.addr_lookups = 0
        self.addr_hits = ()
        self.addr_found = 0
        self.addr_not_local = 0
        self.addr_extra = 0

    # ---- ___init___step27
    def ___init___step27(self, dna, inlet, memory_enabled=True, structure_enabled=True, **extra):
        self.___init___step28(dna, inlet, memory_enabled=memory_enabled, **_rest(extra, ("memory_enabled",)))
        n = dna.state_size
        self.structure_enabled = bool(structure_enabled)

        # the whole-of-relations layer kept its own tables here;
        # it is not part of this Life, and neither are they (see
        # `_str_rebuild_index`).  One Structure logic, one set of tables.

    # ---- ___init___step28
    def ___init___step28(self, dna, inlet, memory_enabled=True, **extra):
        self.___init___step29(dna, inlet, memory_enabled=memory_enabled, **_rest(extra, ("memory_enabled",)))
        # A relation enters activity with participation = one step of learning
        # (mem_lam). It stays in activity for as long as a fresh participation
        # takes to decay to that same one-step level again, so the floor is
        # derived from the learning rate itself and not chosen separately.
        self.mem_floor = float(dna.trace_rate) ** 2
        self.mem_horizon = int(math.log(self.mem_floor) / math.log(1.0 - float(dna.trace_rate))) \
            if 0.0 < float(dna.trace_rate) < 1.0 else 0
        self.mem_front = []
        self.mem_active_front = 0
        self.mem_active_set = []
        self.mem_last_recognized = -1
        self.mem_last_born = -1
        self.mem_search_size = 0
        self.mem_flow_size = 0

    # ---- ___init___step29
    def ___init___step29(self, dna: LifeDNA, inlet, memory_enabled=True, **extra):
        self.___init___step30(dna, inlet, **extra)
        n = dna.state_size
        self.memory_enabled = bool(memory_enabled)
        self.mem_theta = MEM_THETA
        self.mem_rho = float(dna.latent_rate)
        self.mem_lam = float(dna.trace_rate)
        self.mem_margin = float(dna.trace_margin)

        self.bar_d = [0.0] * n
        # One row per relation, and a relation is a Connection: these stand
        # beside `cn_pre` / `cn_post` in the Connection's own id, and are opened
        # by `_mem_open` when a Connection comes about.
        self.mem_s, self.mem_hit = [], []
        self.mem_act, self.mem_act_age = [], []

        self.mem_prev_u = None
        self.mem_inj_prev = None
        self.mem_last_u = None
        self.mem_coeff = []
        self.mem_g_last = []

        self._mem_part_last = {}
        self._mem_part_now = {}

        self.mem_active_touched = 0
        self.mem_active_computed = 0
        self.mem_active_fired = 0
        self.mem_active_fireable = 0
        self.mem_active_set = []
        self.mem_fired_last = ()
        self.mem_frames = self.mem_recognized = 0
        self._mem_have_input = False

        if self.memory_enabled:
            self._detach_old_trace_layer()

    # ---- ___init___step30
    def ___init___step30(self, dna: LifeDNA, inlet, **extra):
        self.___init___step31(dna, inlet, **extra)
        self.thought_growing = False
        self.thought_finished_at = None

    # ---- ___init___step31
    def ___init___step31(self, dna: LifeDNA, inlet, **extra):
        self.___init___step32(dna, inlet, **extra)
        self.internal_trace_weighting = True
        self.last_internal_trace_w = []
        self.last_internal_trace_in = [0.0] * dna.state_size
        self.last_trace_in_old = [0.0] * dna.state_size

    # ---- ___init___step32
    def ___init___step32(self, dna: LifeDNA, inlet, **extra):
        self.___init___step33(dna, inlet, **extra)
        n = dna.state_size
        m = dna.latent_count
        self.thought_coupling = [[0.0] * n for _ in range(m)]
        self.thought_enabled = True
        self.thought_updates = 0
        self.last_thought_feedback = [0.0] * n
        self.last_thought_feedback_norm = 0.0
        self.last_thought_norm = 0.0

    # ---- ___init___step33
    def ___init___step33(self, dna: LifeDNA, inlet, **extra):
        self.___init___step34(dna, inlet, **extra)
        n = dna.state_size
        self.conscious_flow = [0.0] * n
        self.conscious_ticks = 0
        self.conscious_active = False
        self.last_conscious_drive = [0.0] * n
        self.last_conscious_real_drive = [0.0] * n
        self.last_conscious_feedback = [0.0] * n
        self.last_conscious_mode = [1.0] * n
        self.last_conscious_internal = [0.0] * n
        self.last_conscious_trace_in = [0.0] * n
        self.last_conscious_d_internal = [0.0] * n
        self.last_conscious_delta = 0.0

    # ---- ___init___step34
    def ___init___step34(self, dna: LifeDNA, inlet, **extra):
        self.___init___step35(dna, inlet, **extra)
        self._base_dna = dna
        if not hasattr(dna, "source_weights"):
            dna.source_dim = SOURCE_DIM
            dna.source_weights, dna.source_scale, dna.source_seed = \
                make_source_weights(dna, SOURCE_DIM)
        self.source_weights = [list(row) for row in dna.source_weights]
        self.source_dim = int(getattr(dna, "source_dim", SOURCE_DIM))
        self.source_scale = getattr(dna, "source_scale", None)
        self.source_seed = getattr(dna, "source_seed", None)
        self._frame_source = [0.0] * self.source_dim
        self.dna = SourceEntryProxy(dna, self)

    # ---- ___init___step35
    def ___init___step35(self, dna: LifeDNA, inlet, **extra):
        self.___init___step36(dna, inlet, **extra)
        n = dna.state_size
        self.experience_flow = [0.0] * n
        self.last_cue = [0.0] * n

    # ---- ___init___step36
    def ___init___step36(self, dna: LifeDNA, inlet, **extra):
        self.___init___step37(dna, inlet, **extra)
        n = dna.state_size
        self.trace_keys = []
        self.trace_cont = []
        self.trace_born = []
        self.trace_used = []
        self.trace_enabled = True
        self.trace_formation_enabled = True
        self.trace_shaping_enabled = True
        self.trace_injection_on = True
        self.last_trace_age = -10 ** 9
        self.last_trace_g = []
        self.last_trace_w = []
        self.last_trace_in = [0.0] * n
        self.last_trace_fired = 0

    # ---- ___init___step37
    def ___init___step37(self, dna: LifeDNA, inlet, **extra):
        self.___init___step38(dna, inlet, **extra)
        m = dna.latent_count
        n = dna.state_size
        self.latent_activity = [0.0] * m
        self.coupling = [[0.0] * n for _ in range(m)]
        self.growth_enabled = True

    # ---- ___init___step38
    def ___init___step38(self, dna: LifeDNA, inlet, **extra):
        self.___init___step39(dna, inlet, **extra)
        n = dna.state_size
        self.tissue = [0.0] * n
        self.tissue_baseline = [1.0 / n] * n
        self.tissue_enabled = True

    # ---- ___init___step39
    def ___init___step39(self, dna: LifeDNA, inlet, **extra):
        if dna.channel_count != inlet.channel_count:
            raise ValueError("DNA channel count does not match the physical carrier")
        self.dna = dna
        self.inlet = inlet
        self.state = [0.0] * dna.state_size

        self.change_baseline = 0.0
        self.last_delta = 0.0
        self.last_drive = [0.0] * dna.state_size
        self.age = 0

    # ---- the scales this Life's own history holds
    #
    # Everything here answers one kind of question: what does this Life itself
    # already say about what a relation is, what an Element is, what a Structure
    # is, and what state one of its Connections is in.  Each reads only tables
    # the Life has written itself, each costs O(1) at the moment it is asked, and
    # each answers with the fixed constant it replaces while
    # `self_ref_scale_enabled` is off -- so a Life of the round before is judged,
    # value for value, exactly as it was.
    def _own_conn_bar(self):
        """How strongly a relation must hold before this Life calls it acting.

        Read off the Connections this Life has formed: the average of the best
        reading each of them has reached.  A Life that has formed nothing yet
        has no formed sense of what a relation is, and takes any real relation
        at all -- the smallest answer there is, and one its own first
        Connections then replace with what it really found.
        """
        if not self.self_ref_scale_enabled:
            return CH_R2_MIN
        n = len(self.cn_peak)
        if n <= 0:
            return ZERO
        s = getattr(self, "own_peak_sum", None)
        if s is None or getattr(self, "own_peak_n", -1) != n:
            s = sum(self.cn_peak)
            self.own_peak_sum = s
            self.own_peak_n = n
        return s / n

    def _own_break_share(self):
        """How far one of this Life's Connections may fall and still be holding.

        Not a share fixed in advance.  What stands in its place is the weakest
        share this Life has ever found one of its own Connections at **while it
        was still really acting** -- how far its own relations have been seen to
        fall from their own best and still be holding.  Until it has found one,
        it has seen none fall and the share stands at one: a Connection is not
        called broken by falling below anything this Life has ever held, and its
        own first findings are what replace that.
        """
        if not self.self_ref_scale_enabled:
            return SF_BROKEN_SHARE
        share = getattr(self, "own_break_share", 1.0)
        # A relation of this Life can never have been found holding below the
        # share its own strongest relation would only just be holding at: below
        # that, the bar every other part of this file reads "acting" off already
        # says nothing is holding.  The scale therefore cannot be driven under
        # the bar's own normalised share -- which is also what keeps it from
        # sliding towards nothing as a long life goes on, and with it the whole
        # of `broken` sliding away from ever being said.
        top = max(self.cn_peak) if self.cn_peak else 0.0
        if top <= 0.0:
            return share
        floor = self._own_conn_bar() / top
        return share if share > floor else floor

    def _own_st_learn(self, k, live, peak, bar):
        """Note how far a Connection fell while it was still really acting.

        This is where `_own_break_share` is learned: a Connection that is still
        acting -- at the bar this Life's own Connections hold at -- has held its
        own manner, and how far it had fallen from its own best at that moment
        is a share this Life's own relations have been seen to hold at.  A
        Connection that has stopped acting teaches nothing: what is wanted is
        how far a relation of this Life can fall and still be holding, and a
        relation that is not holding has nothing to say about it.

        What is asked is "still holding", and not "still running the way it was
        formed": a relation that has all but gone still runs the way it was
        formed, and taking its share would drive this scale down to nothing --
        after which nothing is ever broken, because everything is still above
        it.  What is taken is the weakest share among the ones that are really
        holding, and that is a floor a Connection really does have to fall past.

        The note is taken and **not** applied.  The state at hand is judged by
        what the moments before it had already held, and this moment's own
        finding goes in with the rest only once the whole pass is over
        (`_own_st_fold`).  So a Connection is never judged against a scale its
        own current reading has just moved: judging first, learning after.
        """
        if not self.self_ref_scale_enabled or peak <= 0.0 or live <= 0.0:
            return
        if live < bar:
            return
        pending = self.own_learn_pending
        if pending is None:
            self.own_learn_pending = pending = []
        pending.append(live / peak)

    def _own_st_fold(self):
        """Put this moment's own lesson in with the rest -- after the judging.

        Called once at the end of a pass of the three ways, when every
        Connection that is judged on this moment has been judged.  From the next
        moment on the scale stands where this moment left it, and not one
        judgement made on this moment was made against it.
        """
        pending = self.own_learn_pending
        if not pending:
            return
        self.own_learn_pending = []
        if not self.self_ref_scale_enabled:
            return
        lo = min(pending)
        if lo < self.own_break_share:
            self.own_break_share = lo

    def _own_dir_floor(self):
        """How definite the other way must be before it is a mismatch.

        Not a magnitude fixed in advance.  What stands in its place is the
        smallest manner this Life has formed a Connection at: "the other way" is
        said only when the other way is at least as definite as the least
        definite relation this Life has itself formed.  A Life that has formed
        none has nothing to measure against, and counts any reversal -- the
        smallest answer there is.
        """
        if not self.self_ref_scale_enabled:
            return SF_DIR_EPS
        lo = getattr(self, "own_form_lo", None)
        return ZERO if lo is None else lo

    def _own_theta(self):
        """How closely an experience must stand to one of this Life's relations.

        Not a closeness fixed in advance.  What stands in its place is the
        average of the matches this Life has itself read: an experience
        continues one of its relations when it stands at least as close to it as
        the experiences it has already had stood to theirs.
        """
        if not self.self_ref_scale_enabled:
            return self.mem_theta
        n = getattr(self, "mem_g_n", 0)
        if n <= 0:
            return ZERO
        return getattr(self, "mem_g_sum", 0.0) / n

    def _own_st_bar(self):
        """How long an organisation must stand before it is a Structure.

        Not a count fixed in advance.  What stands in its place is how long this
        Life's own Structures have run: an organisation is a Structure once it
        has stood at least as long as its own formed Structures have typically
        stood, and never more than `CH_MIN` -- asking for longer than the
        moments this Life's own reading needs before it reads anything at all
        would be asking for something its reading never asks for anywhere else.
        A Life that has formed no Structure yet has only that resolution to go
        by, and its own first Structures are what then move the bar.
        """
        if not self.self_ref_scale_enabled:
            return ST_MIN
        n = len(self.st_frames)
        if n <= 0:
            return CH_MIN
        s = getattr(self, "own_run_sum", None)
        if s is None or getattr(self, "own_run_n", -1) != n:
            s = sum(self.st_frames)
            self.own_run_sum = s
            self.own_run_n = n
        return max(1, min(CH_MIN, int(s / n)))

    def _own_group(self, sa, sb):
        """Whether two units are one Element, by what this Life already holds.

        Off, the base's own rule: their supports overlap by `END_JACCARD` or
        more.  On, the same question asked of the supports themselves -- one of
        them stands **whole** inside the other.  That is the rule the level
        above already uses for a Structure standing whole inside what acts now,
        and it needs no number of its own.
        """
        if not self.self_ref_scale_enabled:
            u = len(sa | sb)
            return bool(u) and len(sa & sb) / u >= END_JACCARD
        return bool(sa) and (sa <= sb or sb <= sa)

    def _own_element(self, ms, ellist):
        """Which Element this Life already has stands whole inside what acts now.

        Off, this answers nothing and the base's own rule stands: the best
        overlap reaching `END_MERGE` is the answer.  On, the Element is the
        answer when it stands **whole** inside the acting group -- every one of
        its own members really taking part here -- and the largest such Element
        is taken.  What the group has grown beyond that is the larger reality
        the Element is standing in this moment, and is not part of its identity.
        """
        if not self.self_ref_scale_enabled:
            return None
        best, size = None, 0
        for i in ellist:
            cur = set(self.el_ends[i])
            if cur and cur <= ms and len(cur) > size:
                best, size = i, len(cur)
        return best

    def _peak_up(self, k, r2):
        """One Connection's own best, moved up, with the sum kept in step."""
        self.own_peak_sum = getattr(self, "own_peak_sum", 0.0) + (
            r2 - self.cn_peak[k])
        self.own_peak_n = len(self.cn_peak)
        self.cn_peak[k] = r2

    def _st_run_inside(self, mem, inner):
        """The longest run any Structure of this Life standing whole here has had.

        An organisation that is still growing changes its own signature with
        every member it takes in, and a count that began again from nothing each
        time would mean the more an organisation grew, the less it could ever
        add up to.  What this piece brings with it is therefore read off what
        this Life has already formed: any Structure of its own that stands whole
        inside the piece hands its own run of moments over.
        """
        if not self.self_ref_scale_enabled:
            return 0
        frozen = self._st_frozen()
        target_mem = set(mem)
        target_edge = set(inner)
        best = 0
        for j in self._st_holders(mem):
            ends, eds = frozen[j]
            if ends <= target_mem and eds <= target_edge:
                if self.st_frames[j] > best:
                    best = self.st_frames[j]
        return best

    def _st_standing_now(self, sid):
        """Whether Structure `sid` stands again on this very moment.

        Read exactly the way this file already reads a Structure running again:
        the organisation it was born with -- every one of its own members and
        every one of its own inner Connections -- standing **whole** inside what
        is acting now.  What the piece has grown beyond that is the larger
        reality the Structure is standing in, and is not part of its identity,
        so the piece is not asked to equal it.  A Structure this Life has never
        formed stands nowhere, and an identity that outlived its own table is
        answered the same way rather than guessed at.
        """
        if not (0 <= sid < len(self.st_ids)):
            return False
        if not (self.only_running_enabled and self.join_on):
            # `_st_step` did not write this moment's own organisation, so there
            # is nothing here to read it against and nothing is said about it
            return True
        now = set(self.st_now_edges)
        nodes = set()
        for a, b in now:
            nodes.add(a)
            nodes.add(b)
        ends, eds = self._st_frozen()[sid]
        return bool(ends) and ends <= nodes and eds <= now

    def _own_state(self, k, ref, live, peak, form, share, floor):
        """Which of the three states this Connection is in now.

        Judged off the Connection itself and the Structure it was really formed
        in, and off nothing else:

          broken    the Connection that was really formed no longer holds: its
                    own reading has fallen past the weakest share this Life has
                    held one of its own relations at while it still held
          mismatch  it does still hold, and yet it can no longer match the
                    organisation of the Structure it was formed in -- either
                    that organisation does not stand again now, or the
                    Connection is running against the very way that organisation
                    gave it, by as much as the least definite manner this Life
                    has formed one at
          stable    it still holds, and it still matches

        Every one of the scales is passed in, not read here: the moment at hand
        is judged by what the moments before it had already held, and the pass's
        own lesson is put in afterwards (`_own_st_fold`).  With
        `self_ref_scale_enabled` off, the constants' own rule stands and nothing
        of the Structure is consulted -- value for value what the round before
        answered.
        """
        if not self.self_ref_scale_enabled:
            if peak > 0.0 and live < SF_BROKEN_SHARE * peak:
                return BROKEN
            if form is not None and abs(form) >= SF_DIR_EPS and form * ref < 0.0:
                return MISMATCH
            return STABLE
        if not (live > 0.0 and live >= share * peak):
            return BROKEN
        if not self._st_standing_now(self.sf_born_in.get(k, -1)):
            return MISMATCH
        if form is not None and abs(form) >= floor and form * ref < 0.0:
            return MISMATCH
        return STABLE

    # ---- _act
    def _act(self):
        """The connections whose own reading is at the bar this moment.

         walks exactly the pairs whose two ends are taking part and keeps
        them in `cn_place`; a connection whose pair it does not walk it leaves
        at zero.  So the acting connections are read straight off that set: the
        judgement is not restated, and this cannot drift away from it.  The
        reading is taken once per moment, and the moment before's is still the
        one standing when a pass of the moment before's turn asks for it.
        """
        if self.act_at == self.ch_steps:
            return self.act_now
        idx = self.cn_index
        live = self.cn_live
        bar = self._own_conn_bar()
        out = []
        for key in self.cn_place:
            k = idx.get(key)
            if k is not None and live[k] >= bar:
                out.append(k)
        out.sort()
        self.act_at = self.ch_steps
        self.act_now = tuple(out)
        return self.act_now

    # ---- _addr_build
    def _addr_build(self):
        """Rebuild every bucket from the Connections the memory already holds."""
        self.addr_buckets = [dict() for _ in range(ADDR_TABLES)]
        self.addr_entries = 0
        for k in range(len(self.cn_key)):
            self._addr_register(k)
        self.addr_builds += 1
        return self.addr_entries

    # ---- _addr_codes
    def _addr_codes(self, vec):
        codes = []
        for t in range(ADDR_TABLES):
            code = 0
            bit = 1
            for plane in self.addr_planes[t]:
                acc = sum(map(_mul, plane, vec))
                if acc >= 0.0:
                    code |= bit
                bit <<= 1
            codes.append(code)
        return codes

    # ---- _addr_lookup
    def _addr_lookup(self, cue):
        self.addr_lookups += 1
        out = []
        seen = set()
        for t, code in enumerate(self._addr_codes(cue)):
            row = self.addr_buckets[t].get(code)
            if not row:
                continue
            for j in row:
                if j not in seen:
                    seen.add(j)
                    out.append(j)
        return out

    # ---- _addr_make_planes
    def _addr_make_planes(self):
        dim = self.addr_dim
        out = []
        for t in range(ADDR_TABLES):
            rng = random.Random((self.addr_seed + 1) * 1000003 + t * 7919 + 104729)
            out.append([[rng.gauss(0.0, 1.0) for _ in range(dim)]
                        for _b in range(ADDR_BITS)])
        return out

    # ---- _addr_register
    def _addr_register(self, k):
        """File one Connection under the experience it came about in.

        A bucket holds relation ids, and a relation is a Connection: the id it
        is filed under is the Connection's own, so a look-up comes back with
        Connections and with nothing else.
        """
        if not self.address_enabled:
            return
        if k >= len(self.cn_key):
            return
        kp = self.cn_key[k]
        if kp is None:
            return
        for t, code in enumerate(self._addr_codes(kp)):
            row = self.addr_buckets[t].get(code)
            if row is None:
                self.addr_buckets[t][code] = [k]
            else:
                row.append(k)
        self.addr_entries += 1

    # ---- _addr_state
    def _addr_state(self):
        sizes = sorted(len(b) for b in self.addr_buckets)
        used = sum(len(b) for b in self.addr_buckets)
        return {"enabled": self.address_enabled,
                "tables": ADDR_TABLES, "bits": ADDR_BITS,
                "registered": self.addr_entries,
                "buckets_used": used, "bucket_slots": ADDR_TABLES * ADDR_BUCKETS,
                "bucket_size_min": sizes[0] if sizes else 0,
                "bucket_size_max": sizes[-1] if sizes else 0,
                "lookups": self.addr_lookups,
                "last_found": self.addr_found,
                "last_not_local": self.addr_not_local,
                "last_extra": self.addr_extra}

    # ---- _align_now
    def _align_now(self):
        """Every table that stands beside `el_ends`, one entry each.

        `el_ends` is what each identity is made of, and it is written when the
        identity is minted and never rewritten.  Read back from a state file it
        is there while the tables that stand beside it are the moment's own: the
        members acting now (`el_now`), the reading of its own channels
        (`el_form`), and the parts it has played (`el_sides`).

        A Life just read back has not acted as any of them yet in this run, so
        the two current tables start empty -- an empty reading, not a made-up
        one, and the first moment that really takes part writes the real one
        over it.  The parts each has played come back from the history; only an
        state file written before they were carried starts empty here.
        """
        n = len(self.el_ends)
        while len(self.el_now) < n:
            self.el_now.append(())
        while len(self.el_form) < n:
            self.el_form.append([])
        while len(self.el_sides) < n:
            self.el_sides.append(set())

    # ---- _base_units
    def _base_units(self):
        """The ends that are not made of anything: the reality, the behaviour,
        and the Life itself."""
        return self._channels() + self.behavior_count + \
            (1 if self._self_unit() >= 0 else 0)

    # ---- __base_units_step1
    def __base_units_step1(self):
        """The units that are not made of anything: the reality, and the Life.

        These are the leaves the reading below stops at.  A Structure's slot is
        not one of them: it stands for an organisation, and what it is really on
        is read through it.
        """
        return self._channels() + (1 if self._self_unit() >= 0 else 0)

    # ---- _behavior_base
    def _behavior_base(self):
        """The first behaviour end.  The reality's channels come before it."""
        return self._channels()

    # ---- _born_out_weights
    def _born_out_weights(self):
        dna = self._base_dna
        rng = random.Random((int(dna.dna_seed) + 1) * 1000003 + OUT_SEED_OFFSET)
        scale = 1.0 / math.sqrt(dna.channel_count)
        return [[rng.gauss(0.0, scale) for _ in range(dna.channel_count)]
                for _ in range(dna.state_size)]

    # ---- _carry_list
    def _carry_list(self):
        """The one list this moment is handed, made if it is not there yet."""
        self._carry_seed()
        if self.walk_carry is None:
            self.walk_carry = Carry()
        return self.walk_carry

    # ---- _carry_on
    def _carry_on(self):
        """Whether the one list is carried here rather than by the layer below.

        The three statements this round reads are 's and 's own, so the
        change stands only where they do.
        """
        return bool(self.carry_enabled and self.join_on and self.join_zero
                    and self.only_running_enabled)

    # ---- _carry_seed
    def _carry_seed(self):
        """Take in a one list that was lived before this implementation was on, once.

        A Life grown with the switch off -- or one read back -- holds the one list
        as a plain list, holds the frame of the moment before, and holds the forms
        of the Structures that are running.  Reading them once is what lets the
        switch be turned on part way through a life: the addresses the moment
        before carried are read off its own frame, and the Structures whose form
        is written are read off `st_form`.  Nothing is changed by reading it.
        """
        if self.walk_carry_seeded:
            return
        self.walk_carry_seeded = True
        cp = self.ch_prev
        if cp:
            self.walk_carried = tuple(u for u, v in enumerate(cp) if v != ZERO)
        r = self.frame_now
        if isinstance(r, Carry):
            self.walk_carry = r
        elif r:
            c = Carry(len(r))
            c.take(r)
            self.walk_carry = c
        else:
            self.walk_carry = Carry(len(cp) if cp else 0)
        self.walk_form_live = tuple(i for i, v in enumerate(self.st_form)
                                    if v != ZERO)

    # ---- _channels
    def _channels(self):
        """The reality is unchanged: still exactly `channel_count` wide."""
        return int(self.dna.channel_count)

    # ---- __channels_step1
    def __channels_step1(self):
        return int(self.dna.channel_count)

    # ---- _cn_issue
    def _cn_issue(self, i, j, live, rr):
        k = len(self.cn_pre)
        self.cn_index[(i, j)] = k
        self.cn_pre.append(i)
        self.cn_post.append(j)
        self.cn_born.append(self.age)
        self.cn_live.append(live)
        self.cn_peak.append(live)
        self.cn_form.append(rr)
        # the totals the deciding scales are read from: what this Life's own
        # Connections hold, and the smallest manner it has formed one at
        self.own_peak_sum = getattr(self, "own_peak_sum", 0.0) + live
        self.own_peak_n = k + 1
        lo = getattr(self, "own_form_lo", None)
        a = abs(rr)
        if lo is None or a < lo:
            self.own_form_lo = a
        self._mem_open(k, rr)
        return k

    # ---- _cn_step
    def _cn_step(self):
        """step, with the two reads of the one list taken off it.

        Two rounds answer this step, and each keeps its own body: the round of
        the three-state history watches the pairs the step walks, before and
        after it, and the round of the permanent addresses reads the one list as
        it is carried rather than at its width.  Whichever stands, the walk, the
        window, the lag, the bar, the issuing and the pairs whose end stopped
        taking part are 's own.
        """
        if self.carry_enabled and self.cn_local_enabled:
            return self._cn_step_carried()
        return self._cn_step_watched()

    # ---- __cn_step_step1
    def __cn_step_step1(self):
        """The moment's connections, judged over the ends taking part now.

        Read as the base reads it, in the same order; the only difference is which
        ordered pairs are walked.  With the switch off this is walk,
        value for value.
        """
        if not self.cn_local_enabled:
            return self.__cn_step_step2()
        r = self.frame_now
        if r is None:
            return
        n = len(r)
        if self.ch_prev is None:
            self.ch_prev = list(r)
            return
        d = [r[i] - self.ch_prev[i] for i in range(n)]
        self.ch_prev = list(r)
        # kept first, then read, exactly as the base has it: what is wanted is
        # the change exactly CH_LAG moments back, and one moment either way is
        # not a
        # small difference on a change sequence that is nearly white.
        self.ch_hist.append(list(d))
        self.ch_steps += 1
        if len(self.ch_hist) < CH_LAG + 1:
            return
        past = self.ch_hist[0]

        # ---- the ends this moment is really made of ---------------------
        # read off the one list  writes: a place that is not running carries
        # exactly 0.0 there, and that is the base's own statement that it is not
        # taking part
        taking = [u for u in range(n) if r[u] != 0.0]
        # what this Life's own Connections say a relation has to hold at
        bar = self._own_conn_bar()

        keys = set()
        for i in taking:
            for j in taking:
                if i == j:
                    continue
                key = (i, j)
                keys.add(key)
                win = self.cn_window.get(key)
                if win is None:
                    win = {"buf": deque(maxlen=CH_WINDOW), "sx": 0.0, "sy": 0.0,
                           "sxx": 0.0, "syy": 0.0, "sxy": 0.0}
                    self.cn_window[key] = win
                buf = win["buf"]
                if len(buf) == CH_WINDOW:
                    ox, oy = buf[0]
                    win["sx"] -= ox
                    win["sy"] -= oy
                    win["sxx"] -= ox * ox
                    win["syy"] -= oy * oy
                    win["sxy"] -= ox * oy
                x, y = past[i], d[j]
                buf.append((x, y))
                win["sx"] += x
                win["sy"] += y
                win["sxx"] += x * x
                win["syy"] += y * y
                win["sxy"] += x * y
                m = len(buf)
                if m < 3:
                    continue
                r2, rr = _r2(win, m)
                self.cn_now[key] = r2
                if key not in self.cn_best or r2 > self.cn_best[key]:
                    self.cn_best[key] = r2
                if m >= CH_MIN and (key not in self.cn_best_full
                                    or r2 > self.cn_best_full[key]):
                    self.cn_best_full[key] = r2
                if key in self.cn_index:
                    k = self.cn_index[key]
                    self.cn_live[k] = r2
                    self.cn_form[k] = rr
                    if r2 > self.cn_peak[k]:
                        self._peak_up(k, r2)
                elif m >= CH_MIN and rr > 0.0 and r2 >= bar:
                    self._cn_issue(i, j, r2, rr)

        # ---- the pairs one of whose ends has stopped taking part --------
        # Their window was evidence about two places acting on each other, and one
        # of them is not acting now: the window goes with it, and a connection
        # running between them reads nothing at this moment.
        for key in self.cn_place - keys:
            del self.cn_window[key]
            self.cn_now[key] = 0.0
            k = self.cn_index.get(key)
            if k is not None:
                self.cn_live[k] = 0.0
                self.cn_form[k] = 0.0
        self.cn_place = keys

    # ---- __cn_step_step2
    def __cn_step_step2(self):
        r = self.frame_now
        if r is None:
            return
        n = len(r)
        if self.ch_prev is None:
            self.ch_prev = list(r)
            return
        d = [r[i] - self.ch_prev[i] for i in range(n)]
        self.ch_prev = list(r)
        # kept first, then read: what is wanted is the change exactly CH_LAG
        # moments back, and one moment either way is not a small difference.
        # A change sequence is nearly white, so a lag that is off by one has
        # almost nothing left to say about the change now.
        self.ch_hist.append(list(d))
        self.ch_steps += 1
        if len(self.ch_hist) < CH_LAG + 1:
            return
        past = self.ch_hist[0]
        bar = self._own_conn_bar()
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                key = (i, j)
                win = self.cn_window.get(key)
                if win is None:
                    win = {"buf": deque(maxlen=CH_WINDOW), "sx": 0.0, "sy": 0.0,
                           "sxx": 0.0, "syy": 0.0, "sxy": 0.0}
                    self.cn_window[key] = win
                buf = win["buf"]
                if len(buf) == CH_WINDOW:
                    ox, oy = buf[0]
                    win["sx"] -= ox
                    win["sy"] -= oy
                    win["sxx"] -= ox * ox
                    win["syy"] -= oy * oy
                    win["sxy"] -= ox * oy
                x, y = past[i], d[j]
                buf.append((x, y))
                win["sx"] += x
                win["sy"] += y
                win["sxx"] += x * x
                win["syy"] += y * y
                win["sxy"] += x * y
                m = len(buf)
                if m < 3:
                    continue
                r2, rr = _r2(win, m)
                self.cn_now[key] = r2
                if key not in self.cn_best or r2 > self.cn_best[key]:
                    self.cn_best[key] = r2
                if m >= CH_MIN and (key not in self.cn_best_full
                                    or r2 > self.cn_best_full[key]):
                    self.cn_best_full[key] = r2
                if key in self.cn_index:
                    k = self.cn_index[key]
                    self.cn_live[k] = r2
                    self.cn_form[k] = rr
                    if r2 > self.cn_peak[k]:
                        self._peak_up(k, r2)
                elif m >= CH_MIN and rr > 0.0 and r2 >= bar:
                    self._cn_issue(i, j, r2, rr)

    # ---- _cn_step_carried
    def _cn_step_carried(self):
        """The round of the addresses: the same step, the frame read as it is.

        The walk, the window, the lag, the bar, the issuing and the pairs whose
        end stopped taking part are and are not restated.  What is
        read differently is the frame: the addresses taking part are the ones the
        frame carries, and the change list is built only where a value really
        moved -- which are the places the moment before carried together with the
        ones this moment carries, everywhere else the change being `0.0` exactly.

        The round before's own reading is taken in the same call -- the pairs the
        moment before was walking, before and after this step -- because this
        layer answers `_cn_step` and that round's layer answered around it.
        """
        r = self.frame_now
        if not isinstance(r, Carry):
            # nothing of this moment has been taken into the one list: the frame
            # standing is the reality's own, and the layer below reads it as it
            # always did
            return self.__cn_step_step1()
        self._carry_seed()
        if not self.sf_runs_enabled:
            self.walk_sf_may = None
            return self._cn_walk(r)
        before = self.cn_place
        out = self._cn_walk(r)
        after = self.cn_place
        if after is before:
            self.walk_sf_may = frozenset()
        else:
            self.walk_sf_may = after | before
        return out

    # ---- _cn_step_watched
    def _cn_step_watched(self):
        """The round of the three-state history: the pairs this step walks, kept.

        The two places that can write a connection's own reading are inside this
        step: the ordered pairs it walks, and the pairs whose end stopped taking
        part (which it zeroes).  Both are read here off the step's own table, so
        the set handed on is the base's own statement and not a filter of it.
        """
        if not self.sf_runs_enabled or not self.cn_local_enabled:
            self.walk_sf_may = None      # not known: every connection is judged
            return self.__cn_step_step1()
        before = self.cn_place
        out = self.__cn_step_step1()
        after = self.cn_place
        if after is before:
            # the step gave up before it walked anything: nothing was written
            self.walk_sf_may = frozenset()
        else:
            self.walk_sf_may = after | before
        return out

    # ---- _cn_walk
    def _cn_walk(self, r):
        """walk, with the frame read as it is carried.

        Verbatim from `src/life_growth_v48` except for three things: the change
        list is built where a value moved rather than by subtracting two lists of
        the whole width, the frame of the moment before is a plain list of the
        same numbers, and the addresses taking part are read off the frame's own
        carrying -- the same set the base read off every address there is.
        """
        n = len(r)
        cp = self.ch_prev
        if cp is None:
            self.ch_prev = r.as_list()
            self.walk_carried = tuple(u for u, v in r.carried().items()
                                      if v != ZERO)
            return None
        carry = r.carried()
        top = len(cp)
        d = [ZERO] * n
        for u in self.walk_carried:
            if 0 <= u < top:
                d[u] = -cp[u]
        for u, v in carry.items():
            if 0 <= u < n:
                d[u] = v - (cp[u] if u < top else ZERO)
        self.ch_prev = r.as_list()
        self.walk_carried = tuple(u for u, v in carry.items() if v != ZERO)
        self.ch_hist.append(list(d))
        self.ch_steps += 1
        if len(self.ch_hist) < CH_LAG + 1:
            return None
        past = self.ch_hist[0]

        taking = r.taking()
        # what this Life's own Connections say a relation has to hold at
        bar = self._own_conn_bar()

        keys = set()
        for i in taking:
            for j in taking:
                if i == j:
                    continue
                key = (i, j)
                keys.add(key)
                win = self.cn_window.get(key)
                if win is None:
                    win = {"buf": deque(maxlen=CH_WINDOW), "sx": ZERO, "sy": ZERO,
                           "sxx": ZERO, "syy": ZERO, "sxy": ZERO}
                    self.cn_window[key] = win
                buf = win["buf"]
                if len(buf) == CH_WINDOW:
                    ox, oy = buf[0]
                    win["sx"] -= ox
                    win["sy"] -= oy
                    win["sxx"] -= ox * ox
                    win["syy"] -= oy * oy
                    win["sxy"] -= ox * oy
                x, y = past[i], d[j]
                buf.append((x, y))
                win["sx"] += x
                win["sy"] += y
                win["sxx"] += x * x
                win["syy"] += y * y
                win["sxy"] += x * y
                m = len(buf)
                if m < 3:
                    continue
                r2, rr = _r2(win, m)
                self.cn_now[key] = r2
                if key not in self.cn_best or r2 > self.cn_best[key]:
                    self.cn_best[key] = r2
                if m >= CH_MIN and (key not in self.cn_best_full
                                    or r2 > self.cn_best_full[key]):
                    self.cn_best_full[key] = r2
                if key in self.cn_index:
                    k = self.cn_index[key]
                    self.cn_live[k] = r2
                    self.cn_form[k] = rr
                    if r2 > self.cn_peak[k]:
                        self._peak_up(k, r2)
                elif m >= CH_MIN and rr > 0.0 and r2 >= bar:
                    self._cn_issue(i, j, r2, rr)

        for key in self.cn_place - keys:
            del self.cn_window[key]
            self.cn_now[key] = ZERO
            k = self.cn_index.get(key)
            if k is not None:
                self.cn_live[k] = ZERO
                self.cn_form[k] = ZERO
        self.cn_place = keys
        return None

    # ---- _cog_step
    def _cog_step(self):
        """One moment: what is brought back is read before the walk.

        The reading uses the moment before's acting and the moment before's
        values, so it is in the list the moment before's way, and the walk of
        this moment finds it there -- exactly as a Structure's slot does.
        """
        if self.one_reality_per_moment_enabled and self.cog_frame is None:
            # No reality of its own this moment.  What is running now is the
            # Life's own activity, inside consciousness (V3.0 6.5): the
            # external frame was taken in once, when it really arrived, and is
            # not handed to the passes a second time as if it were new.
            self.cog_skipped += 1
            return None
        if not getattr(self, "past_run_enabled", False) \
                or not self.cognition_enabled:
            self.pr_skipped += 1
            return self.__cog_step_step1()
        self._pr_step()
        out = self.__cog_step_step1()
        self.pr_moments += 1
        return out

    # ---- __cog_step_step1
    def __cog_step_step1(self):
        if self._self_unit() < 0 or not self.cognition_enabled:
            self.lf_skipped += 1
            return self.__cog_step_step2()
        out = self.__cog_step_step2()
        self.lf_moments += 1
        return out

    # ---- __cog_step_step2   (this file's own: the life-architecture)
    def __cog_step_step2(self):
        """One moment of the life-architecture, and nothing added after it.

        There is no Need layer in this architecture, and LAS is not an
        appendix to anything: the whole moment is

            reality enters  ->  LAS shows  ->  MSIU rebuilds

        and that is `__cog_step_step4` and nowhere else.
        """
        return self.__cog_step_step3()

    # ---- __cog_step_step3   (this file's own: no pass of its own)
    def __cog_step_step3(self):
        """One moment: the base's own, with nothing put between its links."""
        return self.__cog_step_step4()

    # ---- __cog_step_step4
    def __cog_step_step4(self):
        """One moment, in the order the life-architecture runs it.

            reality enters   -- `_take_part`
            LAS shows        -- `_las_step`   (what is really there, and its states)
            MSIU rebuilds    -- `_msiu_step`  (straight off what LAS showed)
            room is made     -- `_form_step`, `_make_room`

        The Life does not run "Connection, then Element, then Structure": that
        is the perspective, and `_cn_step`, `_ends_step`, `_st_step` and
        `_sf_step` are the reading LAS is made of -- they are run inside
        `_las_step` and nothing walks them one after another as a sequence of
        knowing.  What LAS shows, MSIU is handed, with nothing in between.

        `_form_step` and `_make_room` are not a link either: they only put a
        Structure that has just come about into the one list, so that from the
        next moment it takes part like any other end.

        With the recursion switch off this walks exactly the path the base
        walks.
        """
        if not self.recursion_enabled or not self.cognition_enabled:
            self.take_part_skipped += 1
            return self.__cog_step_step5()
        self._take_part()
        out = self.__cog_step_step5()
        if self.msiu_enabled:
            self._msiu_step()
        self._form_step()
        self._make_room()
        self.take_part_moments += 1
        return out

    # ---- __cog_step_step5
    def __cog_step_step5(self):
        """The name the older layer knows this pass by: it is LAS.

        Nothing is run here that `_las_step` does not run.
        """
        return self._las_step()

    # ---- _las_step   (this file's own: LAS, the base display)
    def _las_step(self):
        """LAS: show the whole that is really there this moment, once.

        Reality has just been taken in, and this is the display the Life looks
        at the world through: which Connections are really acting, which
        Elements they make, which Structures those make -- a Structure standing
        inside a larger one included -- and the state of every Connection that
        has one.

        `_cn_step`, `_ends_step`, `_st_step` and `_sf_step` are the reading
        this showing is made of.  They are not links of the Life's own: nothing
        walks them as a sequence of knowing, and nothing is put between them
        and MSIU.

        It shows, and it keeps only the showing (`las_shown`).  It adds
        nothing, chooses nothing and repairs nothing.
        """
        if not self.cognition_enabled:
            return None
        self._cn_step()
        self._ends_step()
        self._st_step()
        self._sf_step()
        self._las_show()
        return None

    # ---- __cog_step_step6
    def __cog_step_step6(self):
        if self.cog_frame is None:
            # no reality of its own this moment -- the base stays as it was
            self.cog_skipped += 1
            return None
        self.cog_steps += 1
        return self.__cog_step_step7()

    # ---- __cog_step_step7
    def __cog_step_step7(self):
        if not self.cognition_enabled:
            return None
        self._cn_step()
        self._ends_step()
        self._st_step()
        return None

    # ---- __cog_step_step8
    def __cog_step_step8(self):
        if not self.cognition_enabled:
            return None
        self._cn_step()
        self._ends_step()
        return None

    # ---- _detach_old_trace_layer
    def _detach_old_trace_layer(self):
        self.trace_formation_enabled = False
        self.trace_shaping_enabled = False
        self.internal_trace_weighting = False

    # ---- _dot
    @staticmethod
    def _dot(u, v):
        acc = 0.0
        for a, b in zip(u, v):
            acc += a * b
        return acc

    # ---- _el_add
    def _el_add(self, i):
        """One identity, minted: it is in the index from this moment on."""
        of = self.el_of
        for u in self.el_ends[i]:
            s = of.get(u)
            if s is None:
                of[u] = s = set()
            s.add(i)
        self.el_of_n = len(self.el_ends)

    # ---- _el_sharing
    def _el_sharing(self, units):
        """The identities that hold at least one of `units`, in the base's order.

        Only those can answer a comparison: an identity sharing nothing with
        the group has an overlap ratio of zero, and the base's own comparison
        takes a strictly greater ratio than the zero it starts from, so an
        identity sharing nothing can never be chosen.  Nothing else is left
        out, so the answer is the base's own.
        """
        self._el_sync()
        of = self.el_of
        out = set()
        for u in units:
            s = of.get(u)
            if s:
                out |= s
        return sorted(out)

    # ---- _el_sync
    def _el_sync(self):
        """Keep the index with `el_ends`, rebuilding it if ever it is behind.

        rule is that identity is frozen and participation is not:
        `el_ends[i]` is written when the identity is minted and never rewritten
        by a later moment.  The index is written in the same place, and if it is
        behind -- a Life grown with the switch off, or one read back -- it is
        built from the table the first time it is asked for.
        """
        if self.el_of_n == len(self.el_ends):
            return
        of = {}
        for i, members in enumerate(self.el_ends):
            for u in members:
                s = of.get(u)
                if s is None:
                    of[u] = s = set()
                s.add(i)
        self.el_of = of
        self.el_of_n = len(self.el_ends)

    # ---- _end_align
    def _end_align(self):
        """It kept `rel_end_pre` / `rel_end_post` as long as the relation
        table.  Those tables are gone, and the load chain still calls this
        once per layer, so it answers what it answered on empty
        tables: nothing.
        """
        return 0

    # ---- _end_edges
    def _end_edges(self):
        """edges, over the connections that are acting now."""
        if not self.now_scope_enabled:
            return self.__end_edges_step1()
        edges = set()
        for k in self._act():
            x = self._end_of_channel(self.cn_pre[k])
            y = self._end_of_channel(self.cn_post[k])
            if x >= 0 and y >= 0 and x != y:
                edges.add((x, y))
        return edges

    # ---- __end_edges_step1
    def __end_edges_step1(self):
        """Which ends act on which, counting only connections that still act."""
        edges = set()
        bar = self._own_conn_bar()
        for k in range(len(self.cn_pre)):
            if self.cn_live[k] < bar:
                continue
            x = self._end_of_channel(self.cn_pre[k])
            y = self._end_of_channel(self.cn_post[k])
            if x >= 0 and y >= 0 and x != y:
                edges.add((x, y))
        return edges

    # ---- _end_of_channel
    def _end_of_channel(self, ch):
        """Which end this unit is acting as **now**.

        The base looks a unit up in the collections it has kept and takes the
        first one that holds it -- and two collections can hold the same unit.
        What is asked here is the identity the current step actually put this
        unit's acting group into, so the graph `_st_step` builds is the graph of
        the acting connections and nothing else.
        """
        if not self.join_on:
            return self.__end_of_channel_step1(ch)
        return self.el_at.get(ch, -1)

    # ---- __end_of_channel_step1
    def __end_of_channel_step1(self, ch):
        for i, mem in enumerate(self.el_ends):
            if ch in mem:
                return i
        return -1

    # ---- _ends_step
    def _ends_step(self):
        """step, on the connections that are acting now.

        The grouping rule is still read on the same pairs (`_now_groups`), so
        what this moment's own relation organisation looks like is read exactly
        as it was.  What it is used for is not the same: **a unit's identity no
        longer comes from the group it is read in.**  Identity belongs to the
        unit itself -- the first moment it really takes part it forms `{u}`, and
        from then on it stands as that one, whatever it is connected to this
        moment and whatever organisation it is standing inside.  What the group
        decides is which Connections act between which units, and through them
        what Structures form; it does not decide who anyone is.
        """
        if not (self.now_scope_enabled and self.join_on):
            return self.__ends_step_step1()
        self.cur_el = []
        self.el_at = {}
        pairs = [(self.cn_pre[k], self.cn_post[k]) for k in self._act()]
        if not pairs:
            return
        sides = {}
        for side, members in self._now_groups(pairs):
            for u in members:
                sides.setdefault(int(u), set()).add(side)
        seen = set()
        for u in sorted(sides):
            members = self._whole_members((u,))
            for side in sorted(sides[u]):
                i = self._keep_end_now(side, members)
                seen.add(i)
                for x in members:
                    self.el_at[int(x)] = i
        for i in seen:
            self.el_frames[i] += 1
        self.cur_el = sorted(seen)

    # ---- _whole_members   (this file's own addition)
    def _whole_members(self, members):
        """A whole taking part here stands for its own contents, not beside them.

        A formed Structure that is taking part this moment is **one** participant
        at the level above.  What is inside it keeps its own place inside it --
        its Connections, its Elements, its Structures and every reading of them
        are not touched, and the base's own rules for all three are unchanged --
        and it is not written beside the whole it belongs to as a member of this
        level's group.  A unit that no whole taking part covers is left as it is.
        Which whole covers a unit is read off the frozen member tables the base
        already keeps (`st_ends` -> `el_ends`), outermost whole first, and
        nothing else is read.
        """
        if not getattr(self, "whole_level_enabled", False):
            return members
        if not self._whole_here():
            return members
        cover = self._whole_cover()
        out = sorted(set(cover.get(u, u) for u in members))
        if len(out) == len(members):
            return members
        return tuple(out)

    # ---- _whole_here   (this file's own addition)
    def _whole_here(self):
        """Which formed Structures are taking part this moment.

        A Structure is a participant at the level above **by its own identity as
        soon as it is running** -- and running is read off `cur_st`, the very
        table `_take_part` reads to decide whose place this moment's one list
        carries.  It is not asked that the Structure's own place have become an
        end of a Connection first: what makes a whole a participant here is that
        it is running now, and nothing else.  Read once a moment and kept.
        """
        stamp = (self.age, len(self.el_ends), len(self.st_ids))
        if self.whole_here_at != stamp:
            self.whole_here_at = stamp
            st_unit = self.st_unit
            got = []
            for i in self.cur_st:
                if 0 <= i < len(st_unit) and st_unit[i] >= 0:
                    j = self.structure_of_unit(st_unit[i])
                    if j >= 0:
                        got.append(j)
            self.whole_here_mem = tuple(got)
        return self.whole_here_mem

    # ---- _whole_cover   (this file's own addition)
    def _whole_cover(self):
        """Which whole covers which unit, and the outermost one where several do.

        A unit that more than one whole taking part covers goes under the whole
        with the more inside it -- the base's own way of putting a unit under the
        group it shares most with.  Read once a moment; a Structure is read as
        itself and is never flattened.  A whole's own unit covers itself, exactly
        as before: a group that is already made of places cannot lose one.
        """
        stamp = (self.age, len(self.el_ends), len(self.st_ids))
        if self.whole_cover_at == stamp:
            return self.whole_cover_mem
        here = self._whole_here()
        inner = self._whole_inner(tuple(self.st_unit[i] for i in here))
        best = {}
        for i in here:
            u = self.st_unit[i]
            got = inner.get(u, ())
            n = len(got)
            for w in got:
                cur = best.get(w)
                if cur is None or n > cur[0]:
                    best[w] = (n, u)
            cur = best.get(u)
            if cur is None or n > cur[0]:
                best[u] = (n, u)
        self.whole_cover_at = stamp
        self.whole_cover_mem = dict((w, v) for w, (_n, v) in best.items())
        return self.whole_cover_mem

    # ---- _whole_inner   (this file's own addition)
    def _whole_inner(self, wholes):
        """What is inside each of those wholes, read off the frozen tables.

        Read once per moment per Structure and kept: the tables it is read off
        only grow when an Element or a Structure is born, and a Structure cannot
        hold one that was born after it, so the reading cannot go round.
        """
        stamp = (self.age, len(self.el_ends), len(self.st_ids))
        if self.whole_inner_at != stamp:
            self.whole_inner_at = stamp
            self.whole_inner_mem = {}
        return dict((u, self._whole_inner_of(self.structure_of_unit(u), set()))
                    for u in wholes)

    # ---- _whole_inner_of   (this file's own addition)
    def _whole_inner_of(self, i, seen):
        """Every unit inside Structure `i`, the contents of its own contents
        included.  A Structure is read as what it is, never flattened: a
        Structure inside it comes back as that Structure's own unit, and what is
        inside *that* one is added on top, all of it read off frozen tables.
        """
        if i < 0 or i >= len(self.st_ids) or i in seen:
            return frozenset()
        got = self.whole_inner_mem.get(i)
        if got is not None:
            return got
        seen.add(i)
        out = set()
        for e in self.st_ends[i]:
            if not (0 <= e < len(self.el_ends)):
                continue
            for w in self.el_ends[e]:
                out.add(w)
                j = self.structure_of_unit(w)
                if j >= 0:
                    out |= self._whole_inner_of(j, seen)
        seen.discard(i)
        out = frozenset(out)
        self.whole_inner_mem[i] = out
        return out

    # ---- __ends_step_step1
    def __ends_step_step1(self):
        """Which Elements this moment is made of: the ones something is at now.

        The base takes every connection it had ever issued; this takes the ones
        whose own reading is at the base's own bar at this moment, and keeps the
        identity each acting group already has.
        """
        if not self.join_on:
            return self.__ends_step_step2()
        self.cur_el = []
        self.el_at = {}
        bar = self._own_conn_bar()
        pairs = [(self.cn_pre[k], self.cn_post[k])
                 for k in range(len(self.cn_live)) if self.cn_live[k] >= bar]
        if not pairs:
            return
        seen = set()
        for side, members in self._now_groups(pairs):
            i = self._keep_end_now(side, members)
            seen.add(i)
            for u in members:
                self.el_at[u] = i
        for i in seen:
            self.el_frames[i] += 1
        self.cur_el = sorted(seen)

    # ---- __ends_step_step2
    def __ends_step_step2(self):
        if not self.cn_index:
            return
        seen_now = set()
        for side in (0, 1):
            support = {}
            for (i, j) in self.cn_index:
                k = i if side == 0 else j
                o = j if side == 0 else i
                support.setdefault(k, set()).add(o)
            keys = sorted(support)
            parent = {k: k for k in keys}

            def find(a):
                while parent[a] != a:
                    parent[a] = parent[parent[a]]
                    a = parent[a]
                return a

            for ai in range(len(keys)):
                for bi in range(ai + 1, len(keys)):
                    a, b = keys[ai], keys[bi]
                    if self._own_group(support[a], support[b]):
                        ra, rb = find(a), find(b)
                        if ra != rb:
                            parent[rb] = ra
            groups = {}
            for k in keys:
                groups.setdefault(find(k), []).append(k)
            for _root, mem in sorted(groups.items()):
                seen_now.add(self._keep_end(side, tuple(sorted(mem))))
        for i in seen_now:
            self.el_frames[i] += 1

    # ---- _form_step
    def _form_step(self):
        """step, asking only the Structures that ran this moment.

        Two rounds answer this pass, and each keeps its own body: the round of
        the Structures and runs asks the Structures that ran and writes the
        same list of forms, and the round of the permanent addresses does the
        same while the one list is carried rather than copied.  Whichever
        stands, the list handed back is the same length and holds the same
        numbers.

        rule answers `0.0` for a Structure that is not running, so
        the call is not made for one.
        """
        if self._carry_on():
            return self._form_step_carrying()
        return self._form_step_at_width()

    # ---- __form_step_step1
    def __form_step_step1(self):
        """What every formed Structure is doing now, and what the Life is.

        Both are readings of this moment's own tables, taken after the walk, and
        both are held for the moment after -- the same way and for the same
        reason a Structure's slot is held from the moment before.
        """
        if not self.st_ids and self._self_unit() < 0:
            return
        want = self.participants()
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < want:
            vals.extend([0.0] * (want - len(vals)))
        self.frame_now = vals
        if self.st_ids:
            self.st_form = [self._structure_own_form(i)
                            for i in range(len(self.st_ids))]
        if self._self_unit() >= 0:
            self.lf_form = self._life_unit_form()

    # ---- __form_step_step2
    def __form_step_step2(self):
        """What every formed Structure is doing now, held in its own slot."""
        if not self.st_ids:
            return
        want = self.participants()
        if len(self.frame_now) < want:
            self.frame_now = list(self.frame_now) + \
                [0.0] * (want - len(self.frame_now))
        self.st_form = [self._structure_own_form(i)
                        for i in range(len(self.st_ids))]

    # ---- _form_step_at_width
    def _form_step_at_width(self):
        """The round of the Structures and runs: the width copied, the forms asked.

         read `cur_st` by copying this table and comparing; this asks only
        the Structures that ran, and every other entry keeps the value the rule
        already gives it.
        """
        if not (self.only_running_enabled and self.join_on and self.join_zero):
            return self.__form_step_step1()
        if not self.st_ids and self._self_unit() < 0:
            return
        want = self.participants()
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < want:
            vals.extend([0.0] * (want - len(vals)))
        self.frame_now = vals
        if self.st_ids:
            form = [0.0] * len(self.st_ids)
            for i in self.cur_st:
                if 0 <= i < len(form):
                    form[i] = self._structure_own_form(i)
            self.st_form = form
        if self._self_unit() >= 0:
            self.lf_form = self._life_unit_form()

    # ---- _form_step_carrying
    def _form_step_carrying(self):
        """The round of the addresses: the same, with the one list carried.

        The list of forms is written where the entries that stop running are put
        back to `0.0` and the ones that are running are set -- so the list is the
        same length and holds the same numbers, and neither it nor the one list
        is made again.
        """
        if not self.st_ids and self._self_unit() < 0:
            return None
        r = self._carry_list()
        r.grow(self.participants())
        if self.st_ids:
            form = self.st_form
            if len(form) < len(self.st_ids):
                form.extend([ZERO] * (len(self.st_ids) - len(form)))
            live = set()
            run = set(self.cur_st)
            for i in run:
                if 0 <= i < len(form):
                    v = self._structure_own_form(i)
                    form[i] = v
                    if v != ZERO:
                        live.add(i)
            for i in self.walk_form_live:
                if i not in run and 0 <= i < len(form):
                    form[i] = ZERO
            self.walk_form_live = tuple(sorted(live))
        if self._self_unit() >= 0:
            self.lf_form = self._life_unit_form()
        return None

    # ---- _grow
    def _grow(self, a, s):
        sigma = self.dna.growth_rate
        if sigma <= 0.0:
            return
        n = len(s)
        m = len(a)
        a_bar = sum(a) / m
        s_bar = sum(s) / n
        da = [v - a_bar for v in a]
        ds = [v - s_bar for v in s]
        ra = math.sqrt(sum(v * v for v in da) / m)
        rs = math.sqrt(sum(v * v for v in ds) / n)
        if ra <= 1e-12:
            ra = 1.0
        if rs <= 1e-12:
            rs = 1.0
        x = [v / ra for v in da]
        inv_m = 1.0 / m
        inv_rs = 1.0 / rs

        A = self.coupling

        pred = [0.0] * n
        for j in range(m):
            xj = x[j]
            if xj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                pred[i] += row[i] * xj

        e = [ds[i] * inv_rs - pred[i] * inv_m for i in range(n)]

        for j in range(m):
            xj = x[j]
            if xj == 0.0:
                continue
            row = A[j]
            g = sigma * xj
            for i in range(n):
                row[i] += g * e[i]

    # ---- _grow_thought
    def _grow_thought(self, a, s):
        sigma = self._base_dna.growth_rate
        if sigma <= 0.0:
            return
        n = len(s)
        m = len(a)
        a_bar = sum(a) / m
        s_bar = sum(s) / n
        da = [v - a_bar for v in a]
        ds = [v - s_bar for v in s]
        ra = math.sqrt(sum(v * v for v in da) / m)
        rs = math.sqrt(sum(v * v for v in ds) / n)
        if ra <= 1e-12:
            ra = 1.0
        if rs <= 1e-12:
            rs = 1.0
        x = [v / ra for v in da]
        inv_m = 1.0 / m
        inv_rs = 1.0 / rs

        T = self.thought_coupling
        pred = [0.0] * n
        for j in range(m):
            xj = x[j]
            if xj == 0.0:
                continue
            row = T[j]
            for i in range(n):
                pred[i] += row[i] * xj
        e = [ds[i] * inv_rs - pred[i] * inv_m for i in range(n)]
        for j in range(m):
            xj = x[j]
            if xj == 0.0:
                continue
            row = T[j]
            g = sigma * xj
            for i in range(n):
                row[i] += g * e[i]
        self.thought_updates += 1

    # ---- _keep_end
    def _keep_end(self, side, members):
        """The base's own call, watched; nothing about it is changed.

        `_keep_end` runs *inside* the moment, before the moment's own count is
        stepped, so what is formed "now" is kept in a list that is emptied as
        each moment begins -- the base's own age cannot be used for that, and
        measuring it showed it: the recorded age is one behind the moment's.
        """
        i = self.__keep_end_step1(side, members)
        words = sorted({self.word_at(u) for u in members
                        if self.word_at(u) is not None})
        self.sp_kept.append((self.age, i, words))
        self.sp_now.append((i, words))
        return i

    # ---- __keep_end_step1
    def __keep_end_step1(self, side, members):
        """The base's own element, and what it was really made of.

        Called by the base for every element it forms or confirms this moment,
        with the ends it is made of.  Nothing here is decided and nothing here
        is written back: the element the base made is returned untouched, and
        who took part in it is kept beside it.
        """
        i = self.__keep_end_step2(side, members)
        seen = self.ow_el_seen.setdefault(i, {"owners": [], "ports": []})
        for u in members:
            o = self.who(u)
            if o not in seen["owners"]:
                seen["owners"].append(o)
            if self.is_port(u) and u not in seen["ports"]:
                seen["ports"].append(u)
        self.ow_kept += 1
        return i

    # ---- __keep_end_step2
    def __keep_end_step2(self, side, members):
        """Keep this end, reusing its identity when it is the same collection.

        The two parts a unit can play are looked at together: what was acting
        in one connection and what was acted on in another are the same thing
        when they are the same channels. That is what makes a participant one
        participant rather than two.

        The tables that stand beside `el_ends` are put in step the same way
        `_keep_end_now` puts them, so a Life read back is answered here too.
        """
        self._align_now()
        ms = set(members)
        best, ov = None, 0.0
        if self.self_ref_scale_enabled:
            best = self._own_element(ms, range(len(self.el_ends)))
        else:
            for i in range(len(self.el_ends)):
                cur = set(self.el_ends[i])
                u = len(ms | cur)
                if u and len(ms & cur) / u > ov:
                    ov, best = len(ms & cur) / u, i
        if best is not None and (self.self_ref_scale_enabled or ov >= END_MERGE):
            if tuple(self.el_ends[best]) != members:
                self.el_grew += 1
                self.el_ends[best] = members
            self.el_form[best] = [self.frame_now[c] for c in members]
            self.el_sides[best].add(side)
            return best
        i = len(self.el_ends)
        self.el_ends.append(members)
        self.el_sides.append({side})
        self.el_born.append(self.age)
        self.el_frames.append(0)
        self.el_form.append([self.frame_now[c] for c in members])
        self.el_issued += 1
        return i

    # ---- _keep_end_now
    def _keep_end_now(self, side, members):
        """Which Element this participant stands as this moment.

        Identity belongs to the unit itself.  A unit that already stands as an
        Element of its own keeps it: what it is connected to this moment, and
        what organisation it stands inside, do not redefine who it is.  What
        answers that is still `_own_element`, and it is asked on **the
        participant's own members** -- so a larger piece standing around it is
        never taken for its identity, while an Element this unit already stands
        as is still itself and is not made again.  A unit that has never really
        taken part forms its own Element here, once, and is that Element from
        then on.
        """
        if not (self.now_scope_enabled and self.join_on):
            return self.__keep_end_now_step1(side, members)
        self._align_now()
        members = tuple(int(u) for u in members)
        ms = set(members)
        best, ov = None, 0.0
        if self.self_ref_scale_enabled:
            best = self._own_element(ms, self._el_sharing(ms))
        else:
            for i in self._el_sharing(ms):
                cur = set(self.el_ends[i])
                u = len(ms | cur)
                if u and len(ms & cur) / u > ov:
                    ov, best = len(ms & cur) / u, i
        if best is not None and (self.self_ref_scale_enabled or ov >= END_MERGE):
            self.el_now[best] = members
            self.el_form[best] = [self.frame_now[c] for c in members]
            self.el_sides[best].add(side)
            return best
        i = len(self.el_ends)
        self.el_ends.append(members)
        self.el_now.append(members)
        self.el_sides.append({side})
        self.el_born.append(self.age)
        self.el_frames.append(0)
        self.el_form.append([self.frame_now[c] for c in members])
        self.el_issued += 1
        self._el_add(i)
        return i

    # ---- __keep_end_now_step1
    def __keep_end_now_step1(self, side, members):
        """The base's own identity rule, writing what is acting now.

        Same comparison, same order, same constant as `_keep_end` -- the only
        difference is where the answer goes: the membership that is acting now
        into `el_now`, while `el_ends` (what this Collection is) is left as it was
        formed.  A group the base would not recognise is a new identity, minted
        exactly as the base mints one.
        """
        self._align_now()
        ms = set(members)
        best, ov = None, 0.0
        if self.self_ref_scale_enabled:
            best = self._own_element(ms, range(len(self.el_ends)))
        else:
            for i in range(len(self.el_ends)):
                cur = set(self.el_ends[i])
                u = len(ms | cur)
                if u and len(ms & cur) / u > ov:
                    ov, best = len(ms & cur) / u, i
        if best is not None and (self.self_ref_scale_enabled or ov >= END_MERGE):
            self.el_now[best] = members
            self.el_form[best] = [self.frame_now[c] for c in members]
            self.el_sides[best].add(side)
            return best
        i = len(self.el_ends)
        self.el_ends.append(members)
        self.el_now.append(members)
        self.el_sides.append({side})
        self.el_born.append(self.age)
        self.el_frames.append(0)
        self.el_form.append([self.frame_now[c] for c in members])
        self.el_issued += 1
        return i

    # ---- _las_connection
    def _las_connection(self, k):
        """One connection, read: what it is, between what, in which state."""
        d = {
            "identity": k,
            "from_element": self._end_of_channel(self.cn_pre[k]),
            "to_element": self._end_of_channel(self.cn_post[k]),
            "born": self.cn_born[k],
            "acts_now": round(self.cn_live[k], 6),
            "strongest_ever": round(self.cn_peak[k], 6),
            "the_way_it_acts_now": round(self.cn_form[k], 6)
            if self.cn_form[k] is not None else None,
        }
        if self.cn_peak[k] > 0.0:
            d["that_is_this_share_of_its_strongest"] = \
                round(self.cn_live[k] / self.cn_peak[k], 6)
        if k in self.sf_way:
            fr = [self.sf_frames.get((k, s), 0)
                  for s in (STABLE, MISMATCH, BROKEN)]
            d["state"] = STATE_NAMES[self.sf_state[k]]
            d["the_way_it_was_formed"] = self.sf_way[k]
            d["moments_in_each_state"] = {"stable": fr[0], "mismatch": fr[1],
                                          "broken": fr[2]}
        else:
            d["state"] = "not judged"
            d["the_way_it_was_formed"] = None
        return d

    # ---- _las_connections_of
    def _las_connections_of(self, mem):
        out = []
        for k in range(len(self.cn_pre)):
            x = self._end_of_channel(self.cn_pre[k])
            y = self._end_of_channel(self.cn_post[k])
            if x != y and x in mem and y in mem:
                out.append(k)
        return out

    # ---- _las_elements
    def _las_elements(self, mem):
        """The elements a whole is made of, as they are right now."""
        out = []
        now = self.frame_now or []
        for e in mem:
            chans = list(self.el_ends[e])
            out.append({
                "identity": e,
                "channels": chans,
                "born": self.el_born[e],
                "seen_moments": self.el_frames[e],
                "acts": 0 in self.el_sides[e],
                "is_acted_on": 1 in self.el_sides[e],
                "is_here_now": bool(now) and any(
                    abs(now[c]) > 0.0 for c in chans),
                "carried_now": [round(now[c], 6) for c in chans] if now else [],
            })
        return out

    # ---- _las_end_of
    def _las_end_of(self, ch):
        return self._end_of_channel(ch)

    # ---- _msiu_words
    def _msiu_words(self, s):
        """One state-directed view said out loud, in the words of the reading."""
        c = s["the_connection"]
        st = s["the_structure"]
        n = s["the_connection"]
        out = []
        kind = n["kind"]
        out.append("connection #%d  %s: between element #%d and "
                   "element #%d, in structure #%d (%s)"
                   % (n["identity"], kind, c["identity"], c["from_element"],
                      c["to_element"], st["identity"],
                      MSIU_KIND_NAMES.get(kind, kind)))
        if kind == "repair":
            out.append("   it is still really acting, but the other way round: "
                       "it acts %.4f of the %.4f it once did, its manner now "
                       "%s where it was formed to run %+d"
                       % (c["acts_now"], c["strongest_ever"],
                          "%+.4f" % c["the_way_it_acts_now"]
                          if c["the_way_it_acts_now"] is not None else "none",
                          c["the_way_it_was_formed"]))
        else:
            out.append("   it does not act any more: it acts %.4f of the %.4f "
                       "it once did, its manner now %s"
                       % (c["acts_now"], c["strongest_ever"],
                          "%+.4f" % c["the_way_it_acts_now"]
                          if c["the_way_it_acts_now"] is not None else "none"))
        chans_of = {e["identity"]: ",".join("ch%d" % x for x in e["channels"])
                    for e in st["elements"]}
        out.append("   both of its ends are still there: element #%d on %s, "
                   "element #%d on %s"
                   % (c["from_element"], chans_of.get(c["from_element"], "-"),
                      c["to_element"], chans_of.get(c["to_element"], "-")))
        out.append("   what is still here: elements %d, connections %d"
                   % (len(st["elements"]), len(st["connections"])))
        for e in st["elements"]:
            out.append("      element #%d  of %s  %s  (seen %d moments, born %d)"
                       % (e["identity"],
                          ",".join("ch%d" % x for x in e["channels"]),
                          "still here now" if e["is_here_now"]
                          else "not seen now", e["seen_moments"], e["born"]))
        for o in st["connections"]:
            out.append("      connection #%d  element #%d -> element #%d  %s  "
                       "acts %.4f, formed to act %s"
                       % (o["identity"], o["from_element"], o["to_element"],
                          o["state"], o["acts_now"],
                          o["the_way_it_was_formed"]
                          if o["the_way_it_was_formed"] is not None
                          else "no established way yet"))
        out.append("   of those connections, still really acting: %s; "
                   "not acting: %s"
                   % ("  ".join("#%d" % c
                                for c in st["connections_still_acting"])
                      or "(none)",
                      "  ".join("#%d" % c
                                for c in st["connections_not_acting"])
                      or "(none)"))
        out.append("   the organisation as formed: %s"
                   % ("  ".join(st["organisation_as_formed"]) or "(none)"))
        if st["it_is_running_as_it_was_formed"]:
            out.append("   that organisation is still running whole"
                       " (%d moments so far)" % st["ran_moments"])
        else:
            out.append("   that organisation no longer runs whole: %s no longer "
                       "run (%d moments in all)"
                       % ("  ".join(st["parts_of_the_organisation_not_running"]),
                          st["ran_moments"]))
        r = s["the_reality_acting_on_it_now"]
        out.append("   the reality on it now: %s"
                   % ("  ".join("%s=%.4f" % (x, v)
                                for x, v in
                                sorted(r["the_channels_these_elements_are_read_on"].items()))
                      or "(nothing read now)"))
        return out

    # ---- _life_unit_form
    def _life_unit_form(self, bar=CH_R2_MIN):
        """reading, over the ends that are acting now.

        The bar is the default one; asked for any other bar the reading is the
        base's own, unchanged, because the acting set here is the one the bar
        names and no other.  What "the default bar" comes to is `_act()`'s own
        answer, which is a fixed reading while `self_ref_scale_enabled` is off
        and this Life's own while it is on.
        """
        if not (self.now_scope_enabled and bar == CH_R2_MIN):
            return self.__life_unit_form_step1(bar)
        vals = self.frame_now or []
        acting = set()
        for k in self._act():
            acting.add(self.cn_pre[k])
            acting.add(self.cn_post[k])
        if not acting:
            return 0.0
        total, n = 0.0, 0
        for e in self._el_sharing(acting):
            members = self.el_ends[e]
            if not members:
                continue
            if not any(u in acting for u in members):
                continue
            s = 0.0
            for u in members:
                if u < len(vals):
                    s += vals[u]
            total += s / len(members)
            n += 1
        return total / n if n else 0.0

    # ---- __life_unit_form_step1
    def __life_unit_form_step1(self, bar=CH_R2_MIN):
        """The Life read as one whole, by the rule this mechanism already uses.

        Over every end that is really acting now -- an end with a member in a
        connection that still acts -- the average of that end's members' current
        values, and then the average of those.  This is the reading the round
        before measured as the one that really goes into connections; a constant
        is read as nothing and an age connects to nothing, and neither is used
        here.

        Nothing is named, ranked or chosen: it is a reading of what is acting,
        taken the way `_structure_own_form` takes a Structure's own form.  A
        moment at which nothing is acting has nothing to read, and reads 0.
        """
        vals = self.frame_now or []
        acting = set()
        for k in range(len(self.cn_pre)):
            if self.cn_live[k] >= bar:
                acting.add(self.cn_pre[k])
                acting.add(self.cn_post[k])
        if not acting:
            return 0.0
        total, n = 0.0, 0
        for e in range(len(self.el_ends)):
            members = self.el_ends[e]
            if not members:
                continue
            if not any(u in acting for u in members):
                continue
            s = 0.0
            for u in members:
                if u < len(vals):
                    s += vals[u]
            total += s / len(members)
            n += 1
        return total / n if n else 0.0

    # ---- _life_unit_index
    def _life_unit_index(self):
        """Where the Life itself sits: after the reality and the behaviour."""
        return self._channels() + self.behavior_count

    # ---- _make_room
    def _make_room(self):
        """A Structure or a run that has just come about is an end from now on.

        The places are given by the layer below, in the order it gives them, and
        the one list answers for the whole address space from here on.  What is not
        done is making the list again: it is widened where it stands, and no place
        is written, because a place that has just appeared has no past and reads
        from nothing.
        """
        if not self._carry_on():
            return self.__make_room_step1()
        if getattr(self, "past_run_enabled", False):
            self._pr_room()
        n = self.participants()
        if self.ch_prev is not None and len(self.ch_prev) < n:
            self.ch_prev.extend([ZERO] * (n - len(self.ch_prev)))
        for h in self.ch_hist:
            if len(h) < n:
                h.extend([ZERO] * (n - len(h)))
        self._carry_list().grow(n)
        return None

    # ---- __make_room_step1
    def __make_room_step1(self):
        """The base's own moment of making room, with the slots in place first.

        The base extends its own tables to the width of the one list; what is
        added here is that a slot is given before the room is made, so a run
        that has just become recallable is an end from the next moment on.
        """
        if not getattr(self, "past_run_enabled", False):
            return self.__make_room_step2()
        self._pr_room()
        return self.__make_room_step2()

    # ---- __make_room_step2
    def __make_room_step2(self):
        """A Structure that has just formed is an end from this moment on.

        The list gets one more slot and the base's own tables are made room for.
        A slot that has just appeared has no past, and that is kept as none: it
        is read from nothing on the moment it appears, so every window it takes
        part in starts there.  Nothing is written for it anywhere else.
        """
        n = self.participants()
        if self.ch_prev is not None and len(self.ch_prev) < n:
            self.ch_prev.extend([0.0] * (n - len(self.ch_prev)))
        for h in self.ch_hist:
            if len(h) < n:
                h.extend([0.0] * (n - len(h)))
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < n:
            vals.extend([0.0] * (n - len(vals)))
        self.frame_now = vals

    # ---- _meet
    def _meet(self, frame):
        """A form the Life has really met, kept with the action it was letting out.

        Only real experience gets in: nothing is preset, and only a single form
        arriving from the world counts as a form.  What is kept is not what the
        form means -- it is what the Life itself was doing when it met it.

         keeps `action_of(self.state)` here.  That is what the Life is
        letting out only while the trunk state is the only source of the act;
        what it is really letting out is `action()`, and that is what is kept
        now.  With no second source open the two are the same thing, value for
        value.
        """
        if not self.expression_enabled:
            return
        if not isinstance(frame, str) or len(frame) != 1:
            return
        act = self.action()
        e = self.expression_forms.get(frame)
        if e is None:
            self.expression_forms[frame] = [list(act), 1.0]
            self.expression_first[frame] = self.expression_met
        else:
            row, w = e
            inv = 1.0 / (w + 1.0)
            for k in range(len(row)):
                row[k] = (row[k] * w + act[k]) * inv
            e[1] = w + 1.0
        # What is kept of the experience is the experience itself: this form
        # was really met while the Life itself was letting this out.  Nothing
        # is averaged away, so a form is not one vector -- the same form can
        # have taken part in different experiences, and the same experience can
        # be met again as a different form (V3.0 8.3).
        if self.expression_experiences_enabled:
            held = self.expression_acts.get(frame)
            if held is None:
                held = []
                self.expression_acts[frame] = held
            held.append(list(act))
            if len(held) > EXPERIENCE_KEEP:
                del held[0]
        self.expression_met += 1

    # ---- __meet_step1
    def __meet_step1(self, frame):
        """A form the Life has really met, kept with the action it was letting out.

        Only real experience gets in: nothing is preset, and only a single form
        arriving from the world counts as a form.  What is kept is not what the
        form means -- it is what the Life itself was doing when it met it.
        """
        if not self.expression_enabled:
            return
        if not isinstance(frame, str) or len(frame) != 1:
            return
        act = self.action_of(self.state)
        e = self.expression_forms.get(frame)
        if e is None:
            self.expression_forms[frame] = [list(act), 1.0]
            self.expression_first[frame] = self.expression_met
        else:
            row, w = e
            inv = 1.0 / (w + 1.0)
            for k in range(len(row)):
                row[k] = (row[k] * w + act[k]) * inv
            e[1] = w + 1.0
        self.expression_met += 1

    # ---- _mem_open   (this file's own: the memory's row for a Connection)
    def _mem_open(self, k, rr):
        """Open the one row the memory keeps for the Connection just issued.

        The memory mints no relation of its own: a relation **is** a Connection,
        and this opens the row that stands beside it, one row per Connection, in
        the Connection's own id.  What it keeps is the experience the Connection
        came about in (`cn_key`, frozen at issue, the way every identity here is
        frozen), the way it first acted (`cn_way`), how much it is in play, and
        the moments it was really continued.  `cn_pre` / `cn_post` / `cn_born` /
        `cn_peak` are read as they stand: there is no second table holding them.
        """
        n = len(self.bar_d)
        u = self.mem_last_u
        self.cn_key.append([float(x) for x in u] if u is not None else [0.0] * n)
        self.cn_way.append(1.0 if rr >= 0.0 else -1.0)
        self.mem_s.append(0.0)
        self.mem_hit.append(0)
        self.mem_act.append(0.0)
        self.mem_act_age.append(self.age)
        self._mem_part_now[k] = 1.0
        for e in (int(self.cn_pre[k]), int(self.cn_post[k])):
            row = self.cn_at.get(e)
            if row is None:
                self.cn_at[e] = [k]
            else:
                row.append(k)
        if self.address_enabled:
            self._addr_register(k)
        return k

    # ---- _mem_index_build   (this file's own: the ends each Connection stands on)
    def _mem_index_build(self):
        """`cn_at`: an end -> the Connections standing on it, in issue order.

        This is the whole of the memory's own index, and it is nothing but the
        Connections read off their own ends.  It is what activation flows along,
        so what a recall reaches is the organisation this Life really formed and
        not a chain the memory kept apart from it.
        """
        at = {}
        for k in range(len(self.cn_pre)):
            for e in (int(self.cn_pre[k]), int(self.cn_post[k])):
                row = at.get(e)
                if row is None:
                    at[e] = [k]
                else:
                    row.append(k)
        self.cn_at = at
        return len(at)

    # ---- _mem_act_now
    def _mem_act_now(self, j):
        if j >= len(self.mem_act):
            return 0.0
        d = self.age - self.mem_act_age[j]
        if d <= 0:
            return self.mem_act[j]
        return self.mem_act[j] * ((1.0 - self.mem_lam) ** d)

    # ---- _mem_apply_participation
    def _mem_apply_participation(self):
        part = self._mem_part_now
        if not part:
            return 0
        lam = self.mem_lam
        age = self.age
        for j, p in part.items():
            self.mem_act[j] = (1.0 - lam) * self._mem_act_now(j) + lam * p
            self.mem_act_age[j] = age
        n_part = len(part)
        self._mem_part_now = {}
        self._mem_part_last = {}
        return n_part

    # ---- _mem_flow
    def _mem_flow(self):
        """Activation travels along the ends the Connections really share.

        The relations this Life is at are the ones acting now; from there the
        stream advances one relation-hop per moment, through the end a place
        stands on, losing per hop exactly what an unused participation loses per
        moment, so it dies out by itself and cannot cover the whole memory.  A
        relation that has gone quiet therefore comes back into play whenever
        what the current Life is doing is still connected to it, and stays out
        when it is not.  What it walks is `cn_pre` / `cn_post` -- the same ends
        every other layer reads -- and not a chain of its own.
        """
        keep = 1.0 - self.mem_lam
        floor = self.mem_floor
        age = self.age
        out = {}
        frontier = []
        for k in self._act():
            if 0 <= k < len(self.mem_act):
                out[k] = 1.0
                frontier.append((k, 1.0))
        while frontier:
            nxt = []
            for k, a in frontier:
                w = a * keep
                if w < floor:
                    continue
                for e in (int(self.cn_pre[k]), int(self.cn_post[k])):
                    row = self.cn_at.get(e)
                    if not row:
                        continue
                    m = row[-1]
                    if m == k or m >= len(self.mem_act):
                        continue
                    if w > out.get(m, 0.0):
                        out[m] = w
                        nxt.append((m, w))
            frontier = nxt
        for k, w in out.items():
            if w > self._mem_act_now(k):
                self.mem_act[k] = w
                self.mem_act_age[k] = age
        self.mem_flow_size = len(out)
        return out


    # ---- _mem_front_extend
    def _mem_front_extend(self, part, flowed=None):
        floor = self.mem_floor
        out = []
        seen = set()
        for j in self.mem_front:
            if self._mem_act_now(j) >= floor:
                out.append(j)
                seen.add(j)
        for j in part:
            if j not in seen:
                out.append(j)
                seen.add(j)
        for j in (flowed or ()):
            if j not in seen and self._mem_act_now(j) >= floor:
                out.append(j)
                seen.add(j)
        self.mem_front = out
        self.mem_active_front = len(out)
        return len(out)

    # ---- _mem_front_seed
    def _mem_front_seed(self):
        floor = self.mem_floor
        self.mem_front = [k for k in range(len(self.mem_act))
                          if self._mem_act_now(k) >= floor]
        self.mem_active_front = len(self.mem_front)
        return self.mem_active_front

    # ---- _ms_issue
    def _ms_issue(self, want):
        """The base's own identity for this organisation, issued if it is new.

        The identity is the organisation itself -- which ends take part and
        which of them acts on which -- exactly the identity  uses.  An
        organisation the base already has is that Structure, confirmed and not
        formed again; one it has never had is issued now, and from this moment
        it takes part in the one list of ends like any other Structure.
        """
        mem, inner = want
        i = self.st_index.get((mem, inner))
        if i is not None:
            return i, False
        i = len(self.st_ids)
        self.st_index[(mem, inner)] = i
        self.st_ids.append(i)
        self.st_ends.append(mem)
        self.st_edges.append(inner)
        self.st_born.append(self.age)
        self.st_frames.append(0)
        self.st_form.append(self._structure_own_form(i))
        self._make_room()
        self.ms_new_structures.append(i)
        return i, True

    # ---- _ms_name
    def _ms_name(self, i):
        if i < 0:
            return "nothing"
        return "structure #%d" % i

    # ---- _ms_new_record
    def _ms_new_record(self, n):
        i = len(self.ms_conn)
        self.ms_index[n["identity"]] = i
        self.ms_conn.append(n["identity"])
        self.ms_kind.append(n["kind"])
        self.ms_connection.append(n["against_connection"])
        self.ms_from_structure.append(n["in_structure"])
        self.ms_born.append(self.age)
        self.ms_first.append(-1)
        self.ms_first_new.append(False)
        self.ms_structure.append(-1)
        self.ms_current.append(True)
        self.ms_moments.append(0)
        self.ms_trail.append([])
        self.ms_ends.append([])
        self.ms_pieces.append([])
        self.ms_left_out.append([])
        return i

    # ---- _ms_words
    def _ms_words(self, r):
        out = []
        c = r["against_connection"]
        out.append("connection #%d  %s  (in structure #%d)"
                   % (r["the_connection"], r["kind"], c, r["in_structure"]))
        out.append("   what it was asked for: %s"
                   % MSIU_KIND_WORDS.get(r["kind"], r["kind"]))
        out.append("   the ends that were still there: %s"
                   % ("  ".join("element #%d" % e
                                for e in r["ends_that_were_still_there"])
                      or "(none)"))
        for p in r["connections_that_still_hold"]:
            out.append("      connection #%d  element #%d -> element #%d  "
                       "still really acting, %.4f"
                       % (p["connection"], p["between_end"], p["and_end"],
                          p["acts_now"]))
        if r["ends_taking_part_in_nothing_that_runs"]:
            out.append("   still there, but taking part in nothing that runs: "
                       "%s"
                       % "  ".join("element #%d" % e
                                   for e in
                                   r["ends_taking_part_in_nothing_that_runs"]))
        if r["formed_first"] < 0:
            out.append("   it was first acted on at %d, and it formed nothing: "
                       "among those ends nothing still really acted"
                       % r["first_acted_at"])
        else:
            out.append("   it was first acted on at %d, and then it formed: %s%s"
                       % (r["first_acted_at"], self._ms_name(r["formed_first"]),
                          "  (a Structure the base had not had before)"
                          if r["that_was_new"] else "  (confirmed, not formed "
                          "again)"))
        if r["still_current"]:
            out.append("   what it forms for it now: %s"
                       % self._ms_name(r["formed_now"]))
        else:
            out.append("   that Connection is not current any more, so MSIU forms "
                       "nothing for it now")
        if len(r["the_answers_it_gave"]) > 1:
            out.append("   and after that, the answers it gave, in order: %s"
                       % "  ".join("at %d %s%s"
                                   % (t, self._ms_name(s),
                                      " (new)" if nw else "")
                                   for t, s, nw
                                   in r["the_answers_it_gave"][1:]))
        out.append("   moments MSIU has acted on that Connection: %d"
                   % r["moments_acted"])
        return out

    # ---- _msiu_answer
    def _msiu_answer(self, n):
        """Form, for this Connection, the organisation its own ends really make now."""
        i = self.ms_index.get(n["identity"])
        if i is None:
            i = self._ms_new_record(n)
        ends, holding, pieces = self._msiu_pieces(n)
        self.ms_ends[i] = ends
        self.ms_pieces[i] = holding
        self.ms_left_out[i] = [u for u in ends
                               if not any(u in (x, y) for x, y, _c in holding)]
        # which piece the connection that asked for the change now takes part
        # in: the one its own end is in, preferring the end it acted from
        k = n["against_connection"]
        pre = self._end_of_channel(self.cn_pre[k])
        post = self._end_of_channel(self.cn_post[k])
        want = None
        for u in (pre, post):
            for mem, inner in pieces:
                if u in mem:
                    want = (mem, inner)
                    break
            if want is not None:
                break
        if want is None:
            formed, new = -1, False
        else:
            formed, new = self._ms_issue(want)
        if self.ms_moments[i] == 0:
            # what it formed the first time it acted on this Connection
            self.ms_first[i] = formed
            self.ms_first_new[i] = new
            self.ms_trail[i].append((self.age, formed, new))
        elif self.ms_structure[i] != formed:
            # an answer that is not the one it last gave, recorded where it
            # changed: a state it goes on answering the same way adds nothing
            self.ms_trail[i].append((self.age, formed, new))
        self.ms_moments[i] += 1
        self.ms_current[i] = True
        self.ms_structure[i] = formed
        return formed

    # ---- _las_show   (this file's own: LAS, the base display)
    def _las_show(self):
        """LAS: what is really there this moment, shown once, in one place.

        Read off the tables the passes above have just written, and off nothing
        else.  What it shows is: every Connection that has a state of its own
        and the state it is in, the Element each of its ends is acting as, the
        Elements themselves, the Structures those Elements make, and the
        recursion -- a Structure whose own place is an end of a larger
        Structure's organisation is shown standing inside that larger one, and
        is not flattened into it.  What is inside it keeps its own place inside
        it (V3.0 3.4, and the rule that a whole is one participant above).

        A Connection that has stopped acting is shown as it is, and not left
        out: a Connection is not only shown while it is still holding, and
        "broken" means exactly a Connection that was really formed and no
        longer holds.  What is acting now is shown beside that, as its own
        reading.

        Nothing is added, chosen, ranked or kept beyond this moment.  This is
        the showing, and it is what MSIU is handed (`_msiu_step`).
        """
        self.las_now = {}
        self.las_shown = {}
        if not self.las_scope_enabled:
            return self.las_shown
        act = list(self._act())
        connections = []
        mismatch, broken = [], []
        for k in sorted(self.sf_way):
            if k >= len(self.cn_pre):
                continue
            st = self.sf_state.get(k)
            pre = self._end_of_channel(self.cn_pre[k])
            post = self._end_of_channel(self.cn_post[k])
            connections.append((k, pre, post, st))
            if st == MISMATCH:
                mismatch.append(k)
            elif st == BROKEN:
                broken.append(k)
        by_element = {}
        for u, e in sorted(self.el_at.items()):
            by_element.setdefault(int(e), []).append(int(u))
        structures = []
        for i in self.cur_st:
            if 0 <= i < len(self.st_ids):
                structures.append((i, tuple(self.st_ends[i]),
                                   tuple(self.st_edges[i])))
        recursion = {}
        for i in range(len(self.st_ids)):
            inner = []
            for e in self.st_ends[i]:
                if not (0 <= e < len(self.el_ends)):
                    continue
                for u in self.el_ends[e]:
                    j = self.structure_of_unit(u)
                    if j >= 0 and j != i:
                        inner.append(j)
            if inner:
                recursion[i] = sorted(set(inner))
        self.las_shown = {
            "moment": self.age,
            "connections": connections,
            "acting": act,
            "elements": dict((e, tuple(sorted(m))) for e, m in by_element.items()),
            "element_of": dict(self.el_at),
            "structures": structures,
            "recursion": recursion,
            "mismatch": mismatch,
            "broken": broken,
        }
        for k in mismatch + broken:
            self.las_now[k] = self._msiu_pieces_of(k)
        return self.las_shown

    # ---- _msiu_pieces   (this file's own)
    def _msiu_pieces(self, n):
        """What LAS has just shown for this Connection, read on this moment.

        Keyed by the Connection itself: a Connection's identity is its own, so
        there is no record between the showing and this reading of it.
        """
        k = n["against_connection"] if "against_connection" in n else n
        got = self.las_now.get(k)
        if got is None:
            return self._msiu_pieces_of(k)
        ends, holding, pieces = got
        return list(ends), list(holding), list(pieces)

    # ---- _msiu_pieces_of   (this file's own)
    def _msiu_pieces_of(self, k):
        """What the ends of the Structure this Connection was formed in do now.

        All of it read: the ends are the ones that Structure is made of, and a
        Connection is a piece while it is really acting this moment.  Nothing
        is added and nothing is chosen.
        """
        sid = self.sf_born_in.get(k, -1)
        ends = list(self.st_ends[sid]) if 0 <= sid < len(self.st_ends) else []
        acting = set(self._act())
        holding = []
        for c in sorted(acting):
            x = self._end_of_channel(self.cn_pre[c])
            y = self._end_of_channel(self.cn_post[c])
            if x in ends and y in ends and x != y:
                holding.append((x, y, c))
        # the connected pieces of that graph, by the base's own rule
        nodes = sorted({u for e in holding for u in e[:2]})
        parent = {u: u for u in nodes}

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for x, y, _c in holding:
            ra, rb = find(x), find(y)
            if ra != rb:
                parent[rb] = ra
        comps = {}
        for u in nodes:
            comps.setdefault(find(u), set()).add(u)
        pieces = []
        for _root, mem in sorted(comps.items()):
            mem = tuple(sorted(mem))
            inner = tuple(sorted((x, y) for x, y, _c in holding
                                 if x in mem and y in mem))
            if inner:
                pieces.append((mem, inner))
        return ends, holding, pieces

    # ---- _msiu_step   (this file's own: MSIU, straight off the showing)
    def _msiu_step(self):
        """MSIU: rebuild, straight off what LAS has just shown.

        The Connections LAS showed as mismatched or broken are the only ones
        MSIU is handed, and a Connection's own identity is the identity here --
        nothing stands between a state and the rebuilding of it, and there is no
        record of any kind in between.

        For each, MSIU forms the organisation its own ends really make now,
        read off the same showing.  What it forms is a Structure like any
        other: it takes part from this moment on, and it is judged, and can be
        rebuilt again, by the same rules as any other.
        """
        self.msiu_moments += 1
        shown = self.las_shown or {}
        here = []
        for kind, ks in ((1, shown.get("mismatch", ())),
                         (2, shown.get("broken", ()))):
            for k in sorted(ks):
                here.append(k)
                self._msiu_answer(self._msiu_asked(k, kind))
        if here:
            self.msiu_acted += 1
        for i in range(len(self.ms_conn)):
            if self.ms_current[i] and self.ms_conn[i] not in here:
                self.ms_current[i] = False

    # ---- _msiu_asked   (this file's own)
    def _msiu_asked(self, k, kind):
        """What MSIU is handed for one Connection LAS showed: the Connection.

        A Connection's identity is its own, so `identity` and
        `against_connection` are the same number here, and nothing is made to
        stand between the state and the rebuilding.
        """
        return {
            "identity": k,
            "kind": kind,
            "against_connection": k,
            "in_structure": self.sf_born_in.get(k, -1),
            "between": [self._end_of_channel(self.cn_pre[k]),
                        self._end_of_channel(self.cn_post[k])],
            "came_about": self.cn_born[k],
            "state_now": STATE_NAMES.get(self.sf_state.get(k), "not judged"),
        }

    # ---- _ms_desc   (this file's own: the record, read out)
    def _ms_desc(self, i):
        """MSIU's own record of one rebuilding, read as it stands.

        The identity is the Connection's own -- there is no separate record of
        a "Need" any more: what MSIU is rebuilding is a Connection LAS showed
        as mismatched or broken, and that Connection's number is its identity
        here (`_msiu_asked`).
        """
        k = self.ms_conn[i]
        return {
            "identity": k,
            "kind": self.ms_kind[i],
            "against_connection": k,
            "between": [self._end_of_channel(self.cn_pre[k]),
                        self._end_of_channel(self.cn_post[k])],
            "in_structure": self.ms_from_structure[i],
            "came_about": self.ms_born[i],
            "from": {"state": STATE_NAMES.get(self.sf_state.get(k),
                                              "not judged")},
            "state_now": STATE_NAMES.get(self.sf_state.get(k), "not judged"),
            "current": bool(self.ms_current[i]),
            "moments_current": self.ms_moments[i],
            "stretches_current": 1 if self.ms_current[i] else 0,
            "stopped": -1,
        }

    # ---- _ms_at   (this file's own)
    def _ms_at(self, n):
        """The record itself, given either its reading or its identity."""
        return self._ms_desc(n) if isinstance(n, int) else n

    # ---- _now_groups
    def _now_groups(self, pairs):
        """`_ends_step`'s own grouping, applied to the acting connections only.

        The base, for each side, gives every unit the set of units it acts on (or
        is acted on by) and merges two units whose sets overlap enough.  This is
        that same loop with `pairs` = the acting connections instead of every
        connection ever issued.  What "enough" is comes from `_own_group`: the
        fixed share `END_JACCARD` while `self_ref_scale_enabled` is off, and one
        support standing whole inside the other while it is on.
        """
        out = []
        for side in (0, 1):
            support = {}
            for (i, j) in pairs:
                k, o = (i, j) if side == 0 else (j, i)
                support.setdefault(k, set()).add(o)
            keys = sorted(support)
            if not keys:
                continue
            parent = {k: k for k in keys}

            def find(a):
                while parent[a] != a:
                    parent[a] = parent[parent[a]]
                    a = parent[a]
                return a

            for ai in range(len(keys)):
                for bi in range(ai + 1, len(keys)):
                    a, b = keys[ai], keys[bi]
                    if self._own_group(support[a], support[b]):
                        ra, rb = find(a), find(b)
                        if ra != rb:
                            parent[rb] = ra
            groups = {}
            for k in keys:
                groups.setdefault(find(k), []).append(k)
            for _root, mem in sorted(groups.items()):
                out.append((side, tuple(sorted(mem))))
        return out

    # ---- _ow_step
    def _ow_step(self):
        """step, over the Structures it has to read again.

        The rule, the tables and every value are the base's own; only the set
        walked is smaller.  It is the Structures just made, plus any Structure
        a frozen member table moved under -- and that second set is read off the
        writing rather than assumed empty.  A Structure already read is read
        again only when one of those tables moved; what is written when it is
        read is a union, exactly as the base writes it, so reading it twice
        cannot write a value once.
        """
        self._walk_seed()
        if not self._ownership_here():
            # no ownership layer on this Life: there are no tables of its here
            # to maintain, and there is nothing for this pass to say
            return None
        self.walk_wrap()
        first = self.ow_st_first
        seen = self.ow_st_seen
        moments = self.ow_st_moments
        port_moments = self.ow_st_port_moments
        el_written = self.el_ends.written
        st_written = self.st_ends.written
        self.walk_frozen_moved += len(el_written) + len(st_written)
        todo = list(range(self.walk_ow_done, len(self.st_ids)))
        self.walk_read_new += len(todo)
        again = set()
        for e in el_written:
            again |= self.walk_el_st.get(e, set())
        for i in st_written:
            again.add(i)
        for i in todo:
            again.discard(i)
        self.walk_read_again += len(again)
        todo.extend(sorted(again))
        self.walk_read_here = set(todo)
        for i in todo:
            if i >= len(self.st_ids):
                continue
            if i not in first:
                first[i] = self.age
            owners, ports = self.st_participants(i)
            got = seen.get(i)
            if got is None:
                seen[i] = got = {"owners": [], "ports": []}
            for o in owners:
                if o not in got["owners"]:
                    got["owners"].append(o)
            for u in ports:
                if u not in got["ports"]:
                    got["ports"].append(u)
            self.walk_note(i)
            if LIFE in owners and i not in self.walk_ow_hold:
                self.walk_ow_hold.append(i)
                self.walk_ow_ports[i] = got["ports"]
        el_written.clear()
        st_written.clear()
        self.walk_ow_done = len(self.st_ids)
        for i in self.walk_ow_hold:
            moments[i] = moments.get(i, 0) + 1
            for u in self.walk_ow_ports[i]:
                k = (i, u)
                port_moments[k] = port_moments.get(k, 0) + 1

    # ---- _ownership_here
    def _ownership_here(self):
        """Whether the ownership layer is on this Life at all.

        The passes this round narrowed read that layer's own tables, which only
        that layer keeps (`own15`'s, in the composition the four rounds were read
        in).  A Life with no ownership layer on it -- `LifeGrowth` alone, which
        is what `src` builds by itself and what `load_life49` brings back -- has
        none of them, so those passes have nothing to maintain and the base's own
        step is left to say what it says.  This is a reading of whether the table
        is there, not a rule: where the layer stands, nothing about the pass
        changes.
        """
        return getattr(self, "ow_st_seen", None) is not None

    # ---- _pr_bringing
    def _pr_bringing(self):
        """bringing, over the connections that were acting then.

        This pass runs before the moment's own judgement, so what it reads is
        the acting of the moment before: the index kept here is the one the
        moment before left standing, which is exactly the set  scans for.
        """
        if not self.now_scope_enabled:
            return self.__pr_bringing_step1()
        out = {}
        for k in self._act():
            e = self.sf_run.get(k)
            if e is None:
                continue
            if not (0 <= e < len(self.rn_unit)) or self.rn_unit[e] < 0:
                continue
            out.setdefault(e, []).append(k)
        return out

    # ---- __pr_bringing_step1
    def __pr_bringing_step1(self):
        """Every run a connection that is really acting now points at.

        Read off the base's own bar and the rounds before, and nothing else:
        a connection counts while it is really acting, and the run it points at
        is the run its own formed way came out of.
        """
        out = {}
        bar = self._own_conn_bar()
        for k in range(len(self.cn_pre)):
            if self.cn_live[k] < bar:
                continue
            e = self.sf_run.get(k)
            if e is None:
                continue
            if not (0 <= e < len(self.rn_unit)) or self.rn_unit[e] < 0:
                continue
            out.setdefault(e, []).append(k)
        return out

    # ---- _pr_give
    def _pr_give(self, kind, ref):
        """Give one thing a slot of its own, once, at the end of the list."""
        u = self._base_units() + len(self.unit_kind)
        self.unit_kind.append(kind)
        self.unit_ref.append(ref)
        if kind == "r":
            self.rn_unit[ref] = u
            self.pr_slots_given += 1
        return u

    # ---- _pr_of
    def _pr_of(self, e):
        """One run, its slot, and what has been happening to it."""
        slot = self.rn_unit[e] if e < len(self.rn_unit) else -1
        bringing = [k for k in range(len(self.cn_pre))
                    if self.sf_run.get(k, -1) == e]
        return {
            "run": e,
            "structure": self.rn_struct[e],
            "ordinal": self.rn_ord[e],
            "start": self.rn_start[e],
            "stop": self.rn_stop[e],
            "still_running": self.rn_stop[e] is None,
            "moments_of_run": self._rn_moments_of(e),
            "slot": slot,
            "given_a_slot": slot >= 0,
            "ways_formed_in_it": sorted(k for k in self.sf_way
                                        if self.sf_run.get(k, -1) == e),
            "connections_that_point_at_it": sorted(bringing),
            "among_those_acting_now": sorted(
                k for k in bringing if self.cn_live[k] >= self._own_conn_bar()),
            "brought_back_now": bool(e < len(self.rn_on) and self.rn_on[e]),
            "brought_back_now_by": list(self.rn_by[e]) if e < len(self.rn_by)
            else [],
            "carries_now": round(self.rn_form[e], 9) if e < len(self.rn_form)
            else 0.0,
            "moments_brought_back": (self.rn_brought[e]
                                     if e < len(self.rn_brought) else 0),
            "stretches_brought_back": [list(x) for x in self.rn_epi[e]]
            if e < len(self.rn_epi) else [],
        }

    # ---- _pr_room
    def _pr_room(self):
        """room, given only to what has not had it.

        A structure is given its slot in the order it was formed and keeps it,
        and a run the moment a way points at it; so what is left to do on a
        later moment is nothing, and nothing is what is walked.
        """
        if not self.now_scope_enabled:
            return self.__pr_room_step1()
        self._pr_seed()
        while len(self.st_unit) < len(self.st_ids):
            self.st_unit.append(-1)
        while len(self.rn_unit) < len(self.rn_start):
            self.rn_unit.append(-1)
        while len(self.rn_form) < len(self.rn_start):
            self.rn_form.append(0.0)
            self.rn_on.append(False)
            self.rn_by.append([])
            self.rn_brought.append(0)
            self.rn_epi.append([])
            self.rn_epi_open.append(False)
        for i in range(self.pr_st_done, len(self.st_ids)):
            if self.st_unit[i] < 0:
                self.st_unit[i] = self._pr_give("s", i)
        self.pr_st_done = len(self.st_ids)
        if self.past_run_all:
            for e in range(self.pr_all_done, len(self.rn_start)):
                if 0 <= e < len(self.rn_unit) and self.rn_unit[e] < 0:
                    self._pr_give("r", e)
            self.pr_all_done = len(self.rn_start)
        elif self.pr_slotless:
            left = set()
            for e in sorted(self.pr_slotless):
                if 0 <= e < len(self.rn_unit) and self.rn_unit[e] < 0:
                    self._pr_give("r", e)
                elif not (0 <= e < len(self.rn_unit)):
                    left.add(e)
            self.pr_slotless = left

    # ---- __pr_room_step1
    def __pr_room_step1(self):
        """Every Structure, and every run that can be brought back, is given
        the slot it is entitled to.

        A Structure that has just formed is an end from this moment on.  A run
        is given an end the moment a formed way points at it, because that is
        the moment there is a route by which it can act at all.  A slot that has
        just appeared has no past, and that is kept as none: it reads zero.
        """
        while len(self.st_unit) < len(self.st_ids):
            self.st_unit.append(-1)
        while len(self.rn_unit) < len(self.rn_start):
            self.rn_unit.append(-1)
        while len(self.rn_form) < len(self.rn_start):
            self.rn_form.append(0.0)
            self.rn_on.append(False)
            self.rn_by.append([])
            self.rn_brought.append(0)
            self.rn_epi.append([])
            self.rn_epi_open.append(False)
        for i in range(len(self.st_ids)):
            if self.st_unit[i] < 0:
                self.st_unit[i] = self._pr_give("s", i)
        if self.past_run_all:
            want = range(len(self.rn_start))
        else:
            want = sorted(set(self.sf_run.values()))
        for e in want:
            if 0 <= e < len(self.rn_unit) and self.rn_unit[e] < 0:
                self._pr_give("r", e)

    # ---- _pr_seed
    def _pr_seed(self):
        """The runs a way already points at, read once, the first time.

        A Life grown with this switch off -- or one read back -- has runs that
        were given their slot by pass; this reads which of them
        still have none, once, and adds nothing to the moment afterwards.
        """
        if self.pr_seeded:
            return
        self.pr_seeded = True
        for e in self.sf_run.values():
            if not (0 <= e < len(self.rn_unit)) or self.rn_unit[e] < 0:
                self.pr_slotless.add(e)

    # ---- _pr_step
    def _pr_step(self):
        """step, clearing and reading only the runs that can move.

        A run's fields are cleared, then set for the runs something is bringing
        back.  A run that was not brought back on the moment before already has
        them empty, so the clearing is done on that set -- which is the set that
        was set, and nothing else.  Which runs are brought back is decided by
        pass and is not restated here.
        """
        if not self.only_running_enabled:
            return self.__pr_step_step1()
        self._walk_seed()
        on, by, form = self.rn_on, self.rn_by, self.rn_form
        for e in self.walk_lit:
            on[e] = False
            by[e] = []
            form[e] = 0.0
        lit = set()
        got = self._pr_bringing()
        for e, ks in got.items():
            total = 0.0
            for k in ks:
                total += 0.5 * (self._pr_was(self.cn_pre[k])
                                + self._pr_was(self.cn_post[k]))
            form[e] = total / len(ks)
            on[e] = True
            by[e] = sorted(ks)
            self.rn_brought[e] += 1
            if not self.rn_epi_open[e]:
                self.rn_epi[e].append([self.age, None])
                self.rn_epi_open[e] = True
                self.walk_stretch.add(e)
                if self.pr_first_back < 0:
                    self.pr_first_back = self.age
            lit.add(e)
        self.walk_lit = lit
        shut = []
        for e in self.walk_stretch:
            if self.rn_epi_open[e] and not on[e]:
                self.rn_epi[e][-1][1] = self.age
                self.rn_epi_open[e] = False
                shut.append(e)
        for e in shut:
            self.walk_stretch.discard(e)
        if got:
            self.pr_bringing += 1

    # ---- __pr_step_step1
    def __pr_step_step1(self):
        """One moment: which runs are brought back, and what each carries.

        A run nothing brings back carries zero and is not acting.  A run that is
        brought back carries the average of the values its bringing connections
        were on, over both ends of each, and then over all of them.

        The acting is read from the moment before, as everything a slot carries
        is, so what is found here is the acting the base judged a moment ago and
        the run is an end for this moment's walk with it.
        """
        for e in range(len(self.rn_unit)):
            self.rn_on[e] = False
            self.rn_by[e] = []
            self.rn_form[e] = 0.0
        got = self._pr_bringing()
        for e, ks in got.items():
            total = 0.0
            for k in ks:
                total += 0.5 * (self._pr_was(self.cn_pre[k])
                                + self._pr_was(self.cn_post[k]))
            self.rn_form[e] = total / len(ks)
            self.rn_on[e] = True
            self.rn_by[e] = sorted(ks)
            self.rn_brought[e] += 1
            if not self.rn_epi_open[e]:
                self.rn_epi[e].append([self.age, None])
                self.rn_epi_open[e] = True
                if self.pr_first_back < 0:
                    self.pr_first_back = self.age
        for e in range(len(self.rn_unit)):
            if self.rn_epi_open[e] and not self.rn_on[e]:
                self.rn_epi[e][-1][1] = self.age
                self.rn_epi_open[e] = False
        if got:
            self.pr_bringing += 1

    # ---- _pr_was
    def _pr_was(self, unit):
        """What a unit was carrying the moment before.

        Read off the base's own table of the moment before -- the same table a
        Structure's slot and the Life unit are read off -- so a run's slot
        carries the moment before, like everything else, and nothing forms a
        circle in the moment it is read.
        """
        p = self.ch_prev
        if p is None or unit >= len(p):
            return 0.0
        return p[unit]

    # ---- _rn_close
    def _rn_close(self, i):
        e = self.__rn_close_step1(i)
        self.walk_going.discard(i)
        return e

    # ---- __rn_close_step1
    def __rn_close_step1(self, i):
        """A Structure that was running is not running: the run stops.

        What is written is only this run's stopping moment.  Everything else the
        run holds -- which Structure, which run of it, when it began -- is left
        exactly as it was, so a later run cannot write over this one.
        """
        e = self.st_run_open[i]
        self.st_run_open[i] = -1
        if e >= 0:
            self.rn_stop[e] = self.age
        return e

    # ---- _rn_moments_of
    def _rn_moments_of(self, e):
        """How many moments a run has lasted so far, as its moments are kept."""
        start = self.rn_start[e]
        stop = self.rn_stop[e]
        return (stop - start) if stop is not None else (self.age - start)

    # ---- _rn_of
    def _rn_of(self, i):
        """One Structure's runs, read as they are."""
        has = i < len(self.st_run_epi)
        eps = self.st_run_epi[i] if has else []
        runs = []
        for e in eps:
            stop = self.rn_stop[e]
            runs.append({"run": e, "ordinal": self.rn_ord[e],
                         "start": self.rn_start[e], "stop": stop,
                         "still_running": stop is None,
                         "moments": self._rn_moments_of(e)})
        return {"structure": i,
                "born": self.st_born[i],
                "moments_run_altogether": self.st_frames[i],
                "runs": len(runs),
                "running_now": (i < len(self.st_run_open)
                                and self.st_run_open[i] >= 0),
                "run_list": runs}

    # ---- _rn_open
    def _rn_open(self, i):
        e = self.__rn_open_step1(i)
        self.walk_going.add(i)
        return e

    # ---- __rn_open_step1
    def __rn_open_step1(self, i):
        """A Structure that was not running is running: a run begins."""
        e = len(self.rn_start)
        self.rn_struct.append(i)
        self.rn_ord.append(self.st_run_ord[i])
        self.rn_start.append(self.age)
        self.rn_stop.append(None)
        self.st_run_epi[i].append(e)
        self.st_run_open[i] = e
        self.st_run_ord[i] += 1
        return e

    # ---- _rn_room
    def _rn_room(self, n):
        """Make room for the runs of every Structure there is now.

        A Structure that has just been issued has no runs, and a run is not
        invented for it here: room is empty and stays empty until it runs.
        """
        while len(self.st_run_epi) < n:
            self.st_run_epi.append([])
            self.st_run_open.append(-1)
            self.st_run_ord.append(0)

    # ---- _rn_step
    def _rn_step(self, before=None, n_before=0):
        """step, on the structures that can cross a run's edge.

        Only a Structure whose own count rose can begin a run, and only a
        Structure whose run is still going can end one -- so those two sets are
        the two that can act.  `before` is not read: whether a count rose is
        noted by the count itself, which is the same answer as comparing it
        against the moment before, without the copy that comparison needs.  The
        comparisons, the order and the counters are 's own.
        """
        if not self.only_running_enabled:
            return self.__rn_step_step1(before, n_before)
        count = self.st_frames
        n = len(count)
        self._rn_room(n)
        rose = count.rose
        for i in sorted(set(self.walk_going) | rose):
            if i >= n:
                continue
            if i in rose:
                if self.st_run_open[i] < 0:
                    self._rn_open(i)
            elif self.st_run_open[i] >= 0:
                self._rn_close(i)
        self.rn_moments += 1

    # ---- __rn_step_step1
    def __rn_step_step1(self, before, n_before):
        """One moment: which Structures the base counted as running now.

        `before` is the base's own count of moments run, taken just before this
        moment's counting; a Structure whose count went up ran this moment.
        """
        n = len(self.st_frames)
        self._rn_room(n)
        for i in range(n):
            was = before[i] if i < n_before else 0
            running = self.st_frames[i] > was
            if running:
                if self.st_run_open[i] < 0:
                    self._rn_open(i)
            elif self.st_run_open[i] >= 0:
                self._rn_close(i)
        self.rn_moments += 1

    # ---- _runs_in_structure
    def _runs_in_structure(self, i):
        """Which runs a Structure's elements reach, read off the base's own
        tables of what it is made of."""
        got = []
        for e in self.st_ends[i]:
            for u in self.el_ends[e]:
                r = self.run_of_unit(u)
                if r >= 0 and r not in got:
                    got.append(r)
        return sorted(got)

    # ---- _self_unit
    def _self_unit(self):
        """The unit that stands for the Life itself, or -1 when that is off."""
        if not getattr(self, "self_perception_enabled", False):
            return -1
        return self._life_unit_index()

    # ---- __self_unit_step1
    def __self_unit_step1(self):
        """The unit that stands for the Life itself, or -1 when the ability
        is off.  One fixed place, kept for the whole of the instance."""
        if not getattr(self, "self_perception_enabled", False):
            return -1
        return self._channels()

    # ---- _sf_judge
    def _sf_judge(self):
        """judgement, on the connections whose reading can have moved.

        The three states are decided exactly as the base decides them, from the same
        three quantities, and every table answers what it answered -- but a
        connection whose own reading has not moved is in the state it was in, so
        there is nothing to write: the stretch it is in lasts until the moment it
        is judged in another state.  The set judged is the base's own pairs whose
        reading can have been written, and nothing else.
        """
        if not self.sf_runs_enabled:
            # whatever the tables hold is the base's own while the switch is off,
            # and is taken in again on the moment the switch is turned back on
            self.walk_sf_wrapped = False
            return self.__sf_judge_step1()
        self.sf_wrap(ahead=1)
        there = self.sf_way
        self.walk_sf_there = len(there)
        if self.walk_sf_may is None:
            moves = list(there)             # not known: every connection judged
        else:
            index = self.cn_index
            moves = [k for k in (index.get(key) for key in self.walk_sf_may)
                     if k is not None and k in there]
            if self.walk_sf_new:
                # a way given on this very moment is judged on it, exactly as the
                # base judges it -- it was not there for the moment before to
                # have judged, and its own reading is this moment's
                have = set(moves)
                moves.extend(k for k in self.walk_sf_new if k not in have)
            moves = sorted(set(moves))
        self.walk_sf_new = set()
        self.walk_sf_walked = len(moves)
        self.walk_sf_skipped = len(there) - len(moves)
        self.walk_sf_last = moves
        n_cn = len(self.cn_pre)
        # the scales this pass judges by, read once, before anything is written:
        # what this moment finds out about itself goes in afterwards, not in
        # between, so no Connection is judged against its own current reading
        share = self._own_break_share()
        floor = self._own_dir_floor()
        bar = self._own_conn_bar()
        for k in moves:
            if k >= n_cn:
                self.walk_sf_left_out += 1
                continue
            ref = there[k]
            live = self.cn_live[k]
            peak = self.cn_peak[k]
            form = self.cn_form[k]
            st = self._own_state(k, ref, live, peak, form, share, floor)
            self._own_st_learn(k, live, peak, bar)
            at = self.walk_sf_at.get(k)
            if at is None:
                # this connection has a way and has been judged, but its history
                # was never taken in: the switch was turned on after this moment
                # had already been counted without it.  The histories are plain
                # lists of one entry per moment then, and the base appends to
                # them directly, so there is nothing here that can put one
                # moment of them in its place -- say so rather than guess.
                raise RuntimeError(
                    "connection %r has been judged %d moment(s) with the switch "
                    "off and its history was not taken in; call sf_wrap() when "
                    "the switch is turned on" % (k, self.sf_moments))
            pos = self.sf_moments - at
            old = self.sf_state.get(k)
            if old is not None and old != st:
                self.sf_changes += 1
            self.sf_state[k] = st
            runs = self._sf_runs_for(k)
            runs["state"].put(st, pos)
            runs["live"].put(live, pos)
            runs["form"].put(form, pos)
            if old != st:
                op = self.walk_sf_open.get(k)
                if op is not None:
                    c = (k, op[0])
                    self.sf_frames[c] = dict.get(self.sf_frames, c, 0) \
                        + (pos - op[1])
                self.walk_sf_open[k] = (st, pos)
        self._own_st_fold()

    # ---- __sf_judge_step1
    def __sf_judge_step1(self):
        # the scales the pass judges by, read before anything is written, and
        # this moment's own lesson put in only once the pass is over
        share = self._own_break_share()
        floor = self._own_dir_floor()
        bar = self._own_conn_bar()
        for k, ref in self.sf_way.items():
            if k >= len(self.cn_pre):
                continue
            live = self.cn_live[k]
            peak = self.cn_peak[k]
            form = self.cn_form[k]
            st = self._own_state(k, ref, live, peak, form, share, floor)
            self._own_st_learn(k, live, peak, bar)
            old = self.sf_state.get(k)
            if old is not None and old != st:
                self.sf_changes += 1
            self.sf_state[k] = st
            self.sf_frames[(k, st)] = self.sf_frames.get((k, st), 0) + 1
            self.sf_hist.setdefault(k, []).append(st)
            self.sf_live_hist.setdefault(k, []).append(live)
            self.sf_form_hist.setdefault(k, []).append(form)
        self._own_st_fold()

    # ---- _sf_recount
    def _sf_recount(self, k, series):
        """One connection's moments, put back where the counts are kept.

        Every judged moment of the connection is one position of its own
        series, so the counts are the stretches themselves: each stretch that
        has ended is added up into the table, and the one still going is not --
        it is answered, as it always is here, from the position the connection
        has reached.  Whatever the base had written for this connection is
        replaced, so that no moment of it is counted twice.
        """
        for c in [c for c in dict.keys(self.sf_frames) if c[0] == k]:
            del self.sf_frames[c]
        val, beg = series.val, series.beg
        for i in range(len(val) - 1):
            c = (k, val[i])
            self.sf_frames[c] = dict.get(self.sf_frames, c, 0) + beg[i + 1] - beg[i]
        if val:
            self.walk_sf_open[k] = (val[-1], beg[-1])

    # ---- _sf_remember
    def _sf_remember(self):
        """The base's own remembering, with the moment a way first appears.

        A way is given to a connection inside this step, and that moment is the
        position its history begins at.  Whether any was given is read off the
        count of ways, so the table is not walked on a moment that gave none.
        """
        if not self.sf_runs_enabled:
            return self.__sf_remember_step1()
        had = len(self.sf_way)
        out = self.__sf_remember_step1()
        if len(self.sf_way) > had:
            at = self.sf_moments            # this step has not counted yet
            for k in self.sf_way:
                if k not in self.walk_sf_at:
                    self.walk_sf_at[k] = at
                    self.walk_sf_new.add(k)
        return out

    # ---- __sf_remember_step1
    def __sf_remember_step1(self):
        """The base's own place for writing a way, watched and not changed.

        The base writes the way and the Structure it was formed in, exactly as
        it did before, and this implementation reads afterwards which connections were
        given a way just now -- and only just now -- so each is pointed at the
        run that was open in this very moment.
        """
        if not self.sf_run_enabled:
            self.sf_run_skipped += 1
            return self.__sf_remember_step2()
        had = len(self.sf_way)
        out = self.__sf_remember_step2()
        if len(self.sf_way) > had:
            left = False
            for k in self.sf_way:
                if k in self.sf_run:
                    continue
                if not self._sr_attribute(k):
                    left = True
            if left:
                self.sf_run_openless += 1
        self.sf_run_moments += 1
        return out

    # ---- __sf_remember_step2
    def __sf_remember_step2(self):
        """Record the way of a connection the first time it is inside a structure."""
        edges = self.st_now_edges
        if not edges:
            return
        nodes = sorted({n for e in edges for n in e})
        parent = {n: n for n in nodes}

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for a, b in edges:
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[rb] = ra
        comps = {}
        for n in nodes:
            comps.setdefault(find(n), []).append(n)
        for _root, mem in comps.items():
            mem = tuple(sorted(mem))
            inner = tuple(sorted(e for e in edges if e[0] in mem and e[1] in mem))
            sid = self.st_index.get((mem, inner))
            if sid is None:
                continue          # not a structure yet: nothing to judge against
            for k in range(len(self.cn_pre)):
                if k in self.sf_way:
                    continue
                x = self._end_of_channel(self.cn_pre[k])
                y = self._end_of_channel(self.cn_post[k])
                if x in mem and y in mem and x != y:
                    f = self.cn_form[k]
                    self.sf_way[k] = -1 if (f is not None and f < 0.0) else 1
                    self.sf_born_in[k] = sid

    # ---- _sf_runs_for
    def _sf_runs_for(self, k):
        got = self.walk_sf_runs.get(k)
        if got is None:
            got = self.walk_sf_runs[k] = {
                "state": Series(self, k), "live": Series(self, k),
                "form": Series(self, k)}
            self.sf_hist[k] = got["state"]
            self.sf_live_hist[k] = got["live"]
            self.sf_form_hist[k] = got["form"]
        return got

    # ---- _sf_step
    def _sf_step(self):
        """One moment of the three ways, for every connection that has one.

        A connection can only be judged against a structure that has really come
        about: before that there is no formed way of running to agree with or to
        depart from.  Once there is one, it stays the way that structure ran, and
        the connection keeps being judged against it -- even after that structure
        itself can no longer run, which is exactly what broken means.
        """
        if not self.state_enabled:
            return
        self._sf_remember()
        if not self.sf_way:
            self.sf_never += 1
            return
        self.sf_moments += 1
        self._sf_judge()

    # ---- _shape
    @staticmethod
    def _shape(v):
        n = len(v)
        bar = sum(v) / n
        d = [x - bar for x in v]
        r = math.sqrt(sum(x * x for x in d))
        if r <= 1e-12:
            return None
        return [x / r for x in d]

    # ---- _sr_attribute
    def _sr_attribute(self, k):
        """writing of a way's run, with the run noted for a slot.

        This is where a run first becomes recallable -- the moment a formed way
        points at it -- so it is where `_pr_room`'s own list gains an entry.
        """
        ok = self.__sr_attribute_step1(k)
        if ok and self.now_scope_enabled:
            self.pr_slotless.add(self.sf_run[k])
        return ok

    # ---- __sr_attribute_step1
    def __sr_attribute_step1(self, k):
        """Give a connection that has just been formed a way its own run.

        The Structure the way was formed in is already written beside it, and
        the run to point at is the run of that Structure open at this instant.
        It is taken as it is or not at all: nothing is guessed and no run is
        made up for a way that has none.
        """
        sid = self.sf_born_in.get(k, -1)
        e = -1 if not (0 <= sid < len(self.st_run_open)) \
            else self.st_run_open[sid]
        if e < 0 or self.rn_struct[e] != sid or self.rn_stop[e] is not None:
            return False
        self.sf_run[k] = e
        self.sf_run_written += 1
        if self.rn_start[e] != self.age:
            self.sf_run_midrun += 1
        return True

    # ---- _st_step
    def _st_step(self):
        """The base's own step, then the ownership layer's, then what ran.

         read `cur_st` by copying the whole of this table before the moment
        and comparing every entry after it, and  copied it again to see
        which Structures ran and open or close their runs.  Neither the copy nor
        the comparison is made here: the layer behind  is entered directly,
        so the base's own step runs and nothing else does, and the two questions
        are answered off the count's own writing.  What reading
        comes to is the Structures whose count moved among the ones the moment
        began with -- a Structure made on this very moment is not one of them,
        and is not read as one here either -- and question is
        whether the count rose.  The rule, the order and every value are the
        base's own.
        """
        self.walk_wrap()
        count = self.st_frames
        if not (self.only_running_enabled and self.join_on):
            count.moved.clear()
            count.rose.clear()
            self.el_ends.written.clear()
            self.st_ends.written.clear()
            return self.__st_step_step1()
        n_before = len(count)
        count.moved.clear()
        count.rose.clear()
        out = self.__st_step_step4()
        self.cur_st = sorted(i for i in count.moved if i < n_before)
        self._rn_step()
        self._ow_step()
        return out

    # ---- __st_step_step1
    def __st_step_step1(self):
        """The base's own step, then whose ports really stand in each structure.

        A structure stands while its organisation does; what is kept here is
        which of the Life's ports have really taken part in it, so a later
        reading can say *through where* the Life was in it and not only that it
        was.
        """
        out = self.__st_step_step2()
        for i in range(len(self.st_ids)):
            if i not in self.ow_st_first:
                self.ow_st_first[i] = self.age
            owners, ports = self.st_participants(i)
            seen = self.ow_st_seen.setdefault(i, {"owners": [], "ports": []})
            for o in owners:
                if o not in seen["owners"]:
                    seen["owners"].append(o)
            for u in ports:
                if u not in seen["ports"]:
                    seen["ports"].append(u)
                if LIFE in owners:
                    k = (i, u)
                    self.ow_st_port_moments[k] = self.ow_st_port_moments.get(k, 0) + 1
            if LIFE in owners:
                self.ow_st_moments[i] = self.ow_st_moments.get(i, 0) + 1
        return out

    # ---- __st_step_step2
    def __st_step_step2(self):
        if not self.join_on:
            self.cur_st = []
            return self.__st_step_step3()
        before = list(self.st_frames)
        out = self.__st_step_step3()
        n = len(self.st_frames)
        self.cur_st = [i for i, v in enumerate(before)
                       if i < n and self.st_frames[i] != v]
        return out

    # ---- __st_step_step3
    def __st_step_step3(self):
        """The base's own moment of reading, and the runs read off it."""
        if not self.run_history_enabled:
            self.rn_skipped += 1
            return self.__st_step_step4()
        before = list(self.st_frames)
        out = self.__st_step_step4()
        self._rn_step(before, len(before))
        return out

    # ---- _st_still_whole   (this file's own addition)
    def _st_still_whole(self, mem, inner, exact):
        """Which formed Structures stand whole inside this moment's own piece.

        A Structure is kept by the organisation it was born with, and it is
        running again as soon as that organisation stands **whole** inside what
        is acting now: every one of its own members really taking part, and
        every one of its own inner Connections still holding between them.  What
        the piece has grown beyond that -- members, Connections, runs, ports --
        is the larger reality the Structure is standing in this moment, and is
        not part of its identity, so the piece is not asked to be equal to it.
        The number does not change, nothing is made in its place, and what is
        inside it is not read and not touched.  Off, nothing is looked for and
        every count is the base's own.
        """
        if not getattr(self, "st_identity_enabled", False):
            return ()
        frozen = self._st_frozen()
        target_mem = set(mem)
        target_edge = set(inner)
        out = []
        for j in self._st_holders(mem):
            if j == exact:
                continue
            ends, eds = frozen[j]
            if ends <= target_mem and eds <= target_edge:
                out.append(j)
        return out

    # ---- _st_holders   (this file's own addition)
    def _st_holders(self, mem):
        """The formed Structures that could stand whole in this piece, and no more.

        All of a Structure's own members have to be taking part for it to stand
        whole here, so its smallest member is one of this piece's members -- and
        every Structure is looked up under its smallest member alone, so this
        costs one short list per member of the piece and nothing else.
        """
        by = self._st_by_end()
        out = []
        for e in mem:
            got = by.get(e)
            if got:
                out.extend(got)
        return out

    # ---- _st_by_end   (this file's own addition)
    def _st_by_end(self):
        """Every formed Structure under its smallest member, read as it is made."""
        n = len(self.st_ids)
        if self.st_by_end_len != n:
            by = {}
            for i in range(n):
                ends = self.st_ends[i]
                if ends:
                    by.setdefault(min(ends), []).append(i)
            self.st_by_end_mem = by
            self.st_by_end_len = n
        return self.st_by_end_mem

    # ---- _st_frozen   (this file's own addition)
    def _st_frozen(self):
        """Each formed Structure's own members and edges, as the sets they are.

        Both tables are written once, when the Structure is born, and read for
        ever, so they are read into sets once per Structure and kept; the table
        is read again only when another Structure is born.
        """
        n = len(self.st_ids)
        if self.st_frozen_len != n:
            self.st_frozen_mem = [(frozenset(self.st_ends[i]),
                                   frozenset(self.st_edges[i]))
                                  for i in range(n)]
            self.st_frozen_len = n
        return self.st_frozen_mem

    # ---- __st_step_step4
    def __st_step_step4(self):
        """One moment of what the connections' organisation shows.

        A structure is one connected piece of the graph of connections between
        ends. It is kept by that organisation, so meeting it again confirms it
        and never forms another one.
        """
        edges = self._end_edges()
        self.st_now_edges = tuple(sorted(edges))
        if not edges:
            self.st_called = -1
            return -1
        nodes = sorted({n for e in edges for n in e})
        parent = {n: n for n in nodes}

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for a, b in edges:
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[rb] = ra
        comps = {}
        for n in nodes:
            comps.setdefault(find(n), set()).add(n)
        called = -1
        for _root, mem in sorted(comps.items()):
            mem = tuple(sorted(mem))
            inner = tuple(sorted(e for e in edges if e[0] in mem and e[1] in mem))
            sig = (mem, inner)
            i = self.st_index.get(sig)
            if i is None:
                # it has to have really run together, again and again, before
                # it is a structure at all -- and how long that is, and what
                # this piece already brings with it, are read off what this Life
                # has itself formed (`_own_st_bar`, `_st_run_inside`)
                n = self.st_pending.get(sig, 0) + 1
                if self.self_ref_scale_enabled:
                    carried = self._st_run_inside(mem, inner)
                    if carried > n:
                        n = carried
                self.st_pending[sig] = n
                if n < self._own_st_bar():
                    i = -1
                else:
                    i = len(self.st_ids)
                    self.st_index[sig] = i
                    self.st_ids.append(i)
                    self.st_ends.append(mem)
                    self.st_edges.append(inner)
                    self.st_born.append(self.age)
                    self.st_frames.append(0)
                    self.own_run_n = i + 1
            if i >= 0:
                self.st_frames[i] += 1
                self.own_run_sum = getattr(self, "own_run_sum", 0) + 1
                called = i
            # a Structure that was formed is running again as soon as the
            # organisation it is kept by stands whole inside this piece -- what
            # the piece has grown beyond it is the larger reality it is in, and
            # is not part of its identity
            for j in self._st_still_whole(mem, inner, i):
                self.st_frames[j] += 1
                self.own_run_sum = getattr(self, "own_run_sum", 0) + 1
                called = j
        self.st_called = called
        return called

    # ---- _start_walks
    def _start_walks(self):
        """The switches and the indexes the four rounds keep, as a life begins.

        Called when a Life is built, and again when one is read back -- a Life
        that lived with a switch off, or one that never had these tables at all,
        begins each of them exactly as a fresh Life of this implementation does.
        """
        # -- the five passes around the connections --------
        self.now_scope_enabled = True
        # this file's own corrections, each standing on its own
        self.one_reality_per_moment_enabled = True
        self.expression_experiences_enabled = True
        self.las_scope_enabled = True
        self.history_enabled = True
        # the scales that decide
        # are this Life's own, read off what it has already formed.  Off, every
        # judgement is the constant's own, value for value.
        self.self_ref_scale_enabled = True
        # what those scales are read from.  Two of them stand for a carried
        # table (`cn_peak`, `st_frames`) and are put back from it the first time
        # they are asked for, so nothing of theirs goes into the state file.
        # The other four are what this run has itself read and cannot be built
        # again out of the history, so they travel in the state file with the
        # history and come back exactly as they stood (`_own_scales_of`).
        self.own_peak_sum = 0.0      # every Connection's own best, added up
        self.own_peak_n = 0          # ... and how many Connections that is
        self.own_run_sum = 0         # the moments this Life's Structures have run
        self.own_run_n = 0           # ... and how many Structures that is
        self.own_form_lo = None      # the smallest manner it has formed one at
        self.own_break_share = 1.0   # the weakest share it held while still holding
        self.mem_g_sum = 0.0         # every match it has read, added up
        self.mem_g_n = 0             # ... and how many moments that is
        # what one pass of the three ways has just found out and not yet put in:
        # it is brought in when that pass is over, so that the moment at hand is
        # judged by the moments before it and never by itself
        self.own_learn_pending = []
        # this file's own addition, and it stands on its own: a formed Structure
        # that is taking part stands at the level above as **one** participant,
        # and what is inside it is left inside it -- its own place is what stands
        # in the group's member table, not its members spread out beside it.
        # Only a Structure that really ran on the moment is taken up this way
        # (`_whole_here`, read off `cur_st`), and the outermost one covers what
        # is inside it.  Off, every group is written member for member exactly as
        # it was before this line existed. Where the
        # other half of what it needs came in: the Structure's own place can only
        # be an end of a Connection if it is carried while it runs, and that is
        # what `st_identity_enabled` below gives it.
        self.whole_level_enabled = True
        self.whole_inner_at = None    # the moment "what is inside" was read on
        self.whole_inner_mem = {}     # Structure -> the units inside it
        self.whole_here_at = None     # the moment "which wholes are here" was read
        self.whole_here_mem = ()      # the Structures running now, in order
        self.whole_cover_at = None    # the moment "which whole covers what" was read
        self.whole_cover_mem = {}     # unit -> the whole that covers it
        # this file's own addition, and it stands on its own: a formed Structure
        # is running again as soon as the organisation it is kept by stands
        # **whole** inside what is acting now -- every member and every inner
        # Connection it was born with, still there.  What the piece has grown
        # beyond that is the larger reality the Structure is standing in and is
        # not part of its identity, so the piece is not asked to equal it.  That
        # is what lets a Structure go on running under its own identity while a
        # larger organisation stands inside it -- and, with the line above, what
        # lets its own place be carried as an end while it does.  Off, nothing is
        # looked for and every count is the base's own..
        self.st_identity_enabled = True
        self.st_by_end_len = -1   # the Structures the index was read for
        self.st_by_end_mem = {}   # smallest member -> the Structures holding it
        self.st_frozen_len = -1   # the Structures whose own tables were read
        self.st_frozen_mem = []   # each one's own members and edges, as sets
        self.las_now = {}         # what LAS shows for this moment, this moment
        self.act_at = None        # the moment the acting set was read on
        self.act_now = ()         # the connections whose reading is at the bar
        self.el_of = {}           # unit -> the identities it is a member of
        self.el_of_n = 0          # identities indexed so far, for the sync check
        self.pr_st_done = 0       # structures up to here have their slot
        self.pr_slotless = set()      # runs a way points at, still without a slot
        self.pr_seeded = False    # the runs already pointed at, read once
        self.pr_all_done = 0      # only used with `past_run_all`

        # -- the Structures and the runs -------------------
        self.only_running_enabled = True
        self.walk_ow_done = 0       # structures whose ownership reading is taken
        self.walk_ow_hold = []      # the structures that hold the Life, in order
        self.walk_ow_ports = {}     # those structures, and the ports they hold
        self.walk_el_st = {}        # element -> the structures it stands in
        self.walk_going = set()     # structures whose run is still going
        self.walk_lit = set()       # runs the moment before brought back
        self.walk_stretch = set()   # runs whose own stretch is going
        self.walk_seeded = False
        self.walk_read_new = 0      # structures read because they were just made
        self.walk_read_again = 0    # structures read again, a frozen table moved
        self.walk_read_here = set()   # the structures read on this very moment
        self.walk_frozen_moved = 0  # times a frozen member table was written
        self.walk_wrap()

        # -- the three-state history -----------------------
        self.sf_runs_enabled = True
        self.walk_sf_at = {}         # connection -> the moment it was first judged
        self.walk_sf_runs = {}       # connection -> its three series
        self.walk_sf_open = {}       # connection -> (state, position it began at)
        self.walk_sf_may = frozenset()   # the pairs whose reading can have moved
        self.walk_sf_new = set()     # connections just given a way
        self.walk_sf_walked = 0      # connections judged on this very moment
        self.walk_sf_skipped = 0     # connections whose own reading did not move
        self.walk_sf_there = 0       # connections that have a way at all
        self.walk_sf_last = ()       # which connections the last moment judged
        self.walk_sf_left_out = 0    # times a judged connection was left out
        self.walk_sf_wrapped = False   # whether the tables have been taken in
        self.sf_wrap()

        # -- the permanent addresses and what is carried ---
        self.carry_enabled = True   # this round's change, as a whole
        self.walk_carry = None      # the one list this moment is handed
        self.walk_carry_seeded = False   # whether a lived list was taken in
        self.walk_carried = ()      # the addresses the moment before carried
        self.walk_form_live = ()    # the Structures whose form is written down
        self.walk_wrote = ()        # the addresses written on this very moment

    # ---- the whole-of-relations layer is not part of this Life -----
    # It was a second Structure logic, standing beside the one this Life really
    # runs on: its own ends (`rel_end_pre` / `rel_end_post`), its own tables
    # (`str_*`), its own step (`_str_step`).  It was already switched off --
    # `structure_enabled` is False, so `_str_step` never ran -- and all that was
    # left of it was what it still wrote into the state file.  It is gone now:
    # this Life has one Connection, one Element and one Structure logic.
    #
    # Kept, because the load chain still calls it once per layer: on
    # tables that are always empty it does what it always did -- nothing.
    def _str_rebuild_index(self):
        return 0

    # ---- _structure_own_form
    def _structure_own_form(self, i):
        """What Structure i is doing now -- and nothing, if it is not running."""
        if not self.join_on:
            return self.__structure_own_form_step1(i)
        if self.join_zero and i not in set(self.cur_st):
            return 0.0
        self._align_now()
        vals = self.frame_now
        total, count = 0.0, 0
        for e in self.st_ends[i]:
            members = self.el_now[e] if 0 <= e < len(self.el_now) else ()
            if not members:
                continue
            s = 0.0
            for u in members:
                s += vals[u]
            total += s / len(members)
            count += 1
        return total / count if count else 0.0

    # ---- __structure_own_form_step1
    def __structure_own_form_step1(self, i):
        """What Structure i is doing now, as this stage reads it.

        This is the one place a Structure's current form comes from, and it is
        deliberately one place.  A Structure is made of elements and an element
        is made of ends, so at this stage it is read the way an element's own
        form is read: the average of its members' own forms, off the same
        activity everything else is read off.

        It is a reading of this stage in a controlled reality, not what a
        Structure is.  A Structure's current form is its own to hold, and when
        it comes from the Structure's own running it will come from here, with
        nothing else about the run moving.
        """
        vals = self.frame_now
        total, count = 0.0, 0
        for e in self.st_ends[i]:
            members = self.el_ends[e]
            if not members:
                continue
            s = 0.0
            for u in members:
                s += vals[u]
            total += s / len(members)
            count += 1
        return total / count if count else 0.0

    # ---- _take_part
    def _take_part(self):
        """Put what is taking part into the one list, and carry nothing else.

        A form that is in the world for the first time is a participant of this
        very moment, so its place is given now, by the layer's own way of giving
        one, and the layer's own making room is called the way it calls it -- not
        one line of that is changed here.

        The rest is the base's own walk.  The reality's channels are the frame
        this moment was handed and are put where they stand.  The behaviour ends
        carry what this Life did, the Life unit carries what it was doing a moment
        ago, a Structure's place carries its own form and a run's place the
        reading it was brought back with -- and only the Structures that are
        running and the runs that were brought back are written at all, because
        every other place holds exactly `0.0` by rule and 's,
        which zeroing loop only wrote down again.  No place is a place
        until the layer behind has given it one.
        """
        if not self._carry_on():
            return self.__take_part_step1()
        pending = getattr(self, "wd_pending", None)
        if pending:
            for name in pending:
                self.wd_unit[name] = self._pr_give(WORD_KIND,
                                                   len(self.wd_order))
                self.wd_order.append(name)
            self.wd_pending = []
            self._make_room()
        src = self.frame_now
        r = self._carry_list()
        if isinstance(src, Carry):
            r.clear()
        else:
            r.take(src if src is not None else ())
        r.grow(self.participants())
        n = len(r)
        wrote = set(r.carried())

        b0 = self._behavior_base()
        bh = self.bh_now
        for i in range(self.behavior_count):
            u = b0 + i
            r[u] = bh[i]
            wrote.add(u)
        u = self._self_unit()
        if u >= 0:
            r[u] = self.lf_form
            wrote.add(u)

        st_unit, st_form = self.st_unit, self.st_form
        for i in self.cur_st:
            if 0 <= i < len(st_unit) and st_unit[i] >= 0:
                u = st_unit[i]
                r[u] = st_form[i]
                wrote.add(u)
        rn_unit, rn_form = self.rn_unit, self.rn_form
        for e in self.walk_lit:
            if 0 <= e < len(rn_unit) and rn_unit[e] >= 0:
                u = rn_unit[e]
                r[u] = rn_form[e]
                wrote.add(u)

        wd_unit = getattr(self, "wd_unit", None)
        if wd_unit:
            for name, v in self.wd_now.items():
                u = wd_unit.get(name, -1)
                if 0 <= u < n:
                    r[u] = v
                    wrote.add(u)
        self.walk_wrote = wrote
        self.frame_now = r
        return None

    # ---- __take_part_step1
    def __take_part_step1(self):
        """The base's own walk, and then what each form carries.

        A form that is in the world for the first time really is a participant
        **this** moment, so its place is taken now rather than at the end of the
        moment: a form's doing is its appearing, and a form that is in the world
        for one moment would otherwise never carry anything at all.  The place
        comes from the base's own `_pr_give`, and the base's own `_make_room` is
        called the way the base calls it.
        """
        if self.wd_pending:
            for name in self.wd_pending:
                self.wd_unit[name] = self._pr_give(WORD_KIND, len(self.wd_order))
                self.wd_order.append(name)
            self.wd_pending = []
            self._make_room()
        self.__take_part_step2()
        vals = self.frame_now
        want = self.participants()
        if vals is None:
            vals = [0.0] * want
        elif len(vals) < want:
            vals = list(vals) + [0.0] * (want - len(vals))
        for name, u in self.wd_unit.items():
            if 0 <= u < len(vals):
                vals[u] = self.wd_now.get(name, 0.0)
        self.frame_now = vals

    # ---- __take_part_step2
    def __take_part_step2(self):
        out = self.__take_part_step3()
        if not (self.join_on and self.join_zero):
            return out
        vals = self.frame_now
        keep = set(self.cur_st)
        for i in range(len(self.st_ids)):
            if i in keep:
                continue
            slot = self.st_unit[i] if i < len(self.st_unit) else -1
            if 0 <= slot < len(vals):
                vals[slot] = 0.0
        for e in range(len(self.rn_unit)):
            if e < len(self.rn_on) and self.rn_on[e]:
                continue
            slot = self.rn_unit[e]
            if 0 <= slot < len(vals):
                vals[slot] = 0.0
        return out

    # ---- __take_part_step3
    def __take_part_step3(self):
        """Put every end into the one list, each at its own place.

        The reality's channels are already in it -- they are the frame this
        moment was handed.  The behaviour ends carry what this Life did, the Life
        unit carries what it was doing a moment ago, a Structure's slot carries
        what that Structure was doing a moment ago, and a run's slot carries the
        reading it was brought back with.  A slot that has not been given yet is
        not written: `_pr_room` gives them, and a Structure or a run that has
        just come about is an end from the next moment on, exactly as before.
        """
        want = self.participants()
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < want:
            vals.extend([0.0] * (want - len(vals)))

        b0 = self._behavior_base()
        for i in range(self.behavior_count):
            vals[b0 + i] = self.bh_now[i]

        u = self._self_unit()
        if u >= 0:
            vals[u] = self.lf_form

        if getattr(self, "past_run_enabled", False):
            # the one list is the slots  hands out; each end goes to its own
            st_unit = self.st_unit
            for i in range(len(self.st_ids)):
                if i < len(st_unit) and st_unit[i] >= 0:
                    vals[st_unit[i]] = self.st_form[i]
            rn_unit = self.rn_unit
            for e in range(len(rn_unit)):
                if rn_unit[e] >= 0:
                    vals[rn_unit[e]] = self.rn_form[e]
        else:
            # the ability is off: no slots were ever handed out, so the
            # Structures sit one after another, as the base lays them out
            off = self._base_units()
            for i in range(len(self.st_ids)):
                vals[off + i] = self.st_form[i]

        self.frame_now = vals

    # ---- __take_part_step4
    def __take_part_step4(self):
        """Put what the reality, the behaviour, the Life and each formed
        Structure are doing into the one list.

        The reality's channels are already in it -- they are the frame this
        moment was handed.  The behaviour ends carry what this Life did, the Life
        unit carries what it was doing a moment ago, and each Structure's slot
        carries its own form; all of them read from the moment before, so nothing
        forms a circle.
        """
        want = self.participants()
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < want:
            vals.extend([0.0] * (want - len(vals)))
        b0 = self._behavior_base()
        for i in range(self.behavior_count):
            vals[b0 + i] = self.bh_now[i]
        u = self._self_unit()
        if u >= 0:
            vals[u] = self.lf_form
        off = self._base_units()
        for i in range(len(self.st_ids)):
            vals[off + i] = self.st_form[i]
        self.frame_now = vals

    # ---- __take_part_step5
    def __take_part_step5(self):
        """The base's own walk, with every slot written where it really is.

        A Structure's slot is written with what the Structure is doing, and a
        run's slot with the reading it carries -- the moment before's, as a
        Structure's is.
        """
        if not getattr(self, "past_run_enabled", False):
            return self.__take_part_step6()
        want = self.participants()
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < want:
            vals.extend([0.0] * (want - len(vals)))
        u = self._self_unit()
        if u >= 0:
            vals[u] = self.lf_form
        for i in range(len(self.st_ids)):
            if i < len(self.st_unit) and self.st_unit[i] >= 0:
                vals[self.st_unit[i]] = self.st_form[i]
        for e in range(len(self.rn_unit)):
            if self.rn_unit[e] >= 0:
                vals[self.rn_unit[e]] = self.rn_form[e]
        self.frame_now = vals

    # ---- __take_part_step6
    def __take_part_step6(self):
        """Put what the Life is and what each formed Structure is doing into
        the one list.

        The Life unit carries what it was doing a moment ago, so nothing forms
        a circle; the reading for this moment is taken after the walk.
        """
        want = self.participants()
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < want:
            vals.extend([0.0] * (want - len(vals)))
        ch = self._channels()
        u = self._self_unit()
        off = ch
        if u >= 0:
            vals[u] = self.lf_form
            off = u + 1
        for i in range(len(self.st_ids)):
            vals[off + i] = self.st_form[i]
        self.frame_now = vals

    # ---- __take_part_step7
    def __take_part_step7(self):
        """Put what each formed Structure is doing into the one list.

        One slot each, right after the channels, in the order the Structures
        were given their identity.  Nothing is decided and nothing is declared
        here: a Structure that has really run together as an organisation is a
        slot, and a slot is an end.
        """
        want = self.participants()
        vals = list(self.frame_now) if self.frame_now else []
        if len(vals) < want:
            vals.extend([0.0] * (want - len(vals)))
        ch = self._channels()
        for i in range(len(self.st_ids)):
            vals[ch + i] = self.st_form[i]
        self.frame_now = vals

    # ---- _walk_seed
    def _walk_seed(self):
        """Read the going things once, in case the switch was turned on late.

        A Life grown with the switch off -- or one read back -- has its counts,
        its open runs and its brought-back runs written by the base's own
        passes, and the ownership layer's own step has already read every
        Structure there is.  What is going is read off those tables once and
        taken into the indexes here; a fresh Life has nothing to read and this
        adds nothing.
        """
        if self.walk_seeded:
            return
        self.walk_seeded = True
        seen = self.ow_st_seen if self._ownership_here() else {}
        for i in range(len(self.st_ids)):
            self.walk_note(i)
        for i in sorted(seen):
            got = seen[i]
            if LIFE in got["owners"]:
                self.walk_ow_hold.append(i)
                self.walk_ow_ports[i] = got["ports"]
        self.walk_ow_done = len(self.st_ids)
        self.walk_going = set(i for i in range(len(self.st_run_open))
                              if self.st_run_open[i] >= 0)
        self.walk_lit = set(e for e in range(len(self.rn_on)) if self.rn_on[e])
        self.walk_stretch = set(e for e in range(len(self.rn_epi_open))
                                if self.rn_epi_open[e])
        self.el_ends.written.clear()
        self.st_ends.written.clear()

    # ---- _write_tissue
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

    # ---- action
    def action(self):
        """What the whole Life is letting out right now.

        One reading and no choice: what the Life is doing, with what is really
        standing in it.  The Life's own running is always there (`self.state`),
        and what is really standing this moment -- the Structures taking part
        now -- is laid where it really is; both go out through the same innate
        passage (`action_of`).

        There is no longer a pass between sources here.  The thinking result,
        a chosen Structure, the own act and the two together were four answers
        to one question, and the answer is one: the Life's own running, with
        what stands in it.  Nothing is chosen, ranked or preferred, and no
        switch picks a source.
        """
        return self.action_of(self._standing_form())

    # ---- _standing_form   (this file's own)
    def _standing_form(self):
        """What is really standing now, as one reading of the Life.

        The Life's own running, plus the doing of every Structure taking part
        this moment, laid where it really is.  A Structure that is not taking
        part writes nothing; if more than one is standing, they are all of
        them.
        """
        src = list(self.state)
        frame = self._organisation_frame()
        if _norm(frame) > 1e-12:
            drive = self._base_dna.entry_drive(frame)
            for i in range(min(len(src), len(drive))):
                src[i] += drive[i]
        return src

    # ---- _organisation_frame   (this file's own)
    def _organisation_frame(self):
        """The Structures taking part this moment, laid where they really are.

        Read off `cur_st` -- the Structures this moment's own step found
        running -- and off `st_form`, which is what each of them is doing.
        Nothing is read from MSIU's records here: what stands is what stands,
        whoever it was that formed it.
        """
        n = self._base_units()
        frame = [0.0] * n
        for i in self.cur_st:
            if not (0 <= i < len(self.st_form)):
                continue
            v = self.st_form[i]
            if v == 0.0:
                continue
            for c in self.structure_reach(i):
                if 0 <= c < n:
                    frame[c] += v
        u = self._self_unit()
        if 0 <= u < n:
            frame[u] = self.lf_form
        return frame

    # ---- _action_step1
    def _action_step1(self):
        """What the Life is letting out right now.

        When MSIU has formed a Structure, what comes out is what that Structure
        is doing.  Otherwise this is act, and nothing about it is
        touched: the thinking result if one has formed, and the current activity
        if not.  A formed Structure that carries nothing is not a source, and
        's act stands.
        """
        if self.structure_action_enabled:
            if self.structures_msiu_formed_now():
                src = self.structure_source()
                if _norm(src) > 1e-12:
                    return self.action_of(src)
        return self._action_step2()

    # ---- _action_step2
    def _action_step2(self):
        """What the Life is letting out right now.

        When a thinking result has formed, the action comes from it; otherwise it
        comes from the current activity.  (This implementation verifies the first way.)
        """
        if self.thought_has_result():
            src = self.thought_source()
            if _norm(src) > 1e-12:
                return self.action_of(src)
        return self.action_of(self.state)

    # ---- action_of
    def action_of(self, v):
        """The passage from an internal activity to an action.

        The action is only what the Life is letting out.  It is not a character,
        it carries no name and no meaning, and nothing goes back up this passage.
        """
        k = self._base_dna.channel_count
        out = [0.0] * k
        for i, row in enumerate(self.out_weights):
            vi = v[i]
            if vi == 0.0:
                continue
            for c in range(k):
                out[c] += row[c] * vi
        return out

    # ---- adopt_state
    def adopt_state(self, other):
        if len(other.state) != self.state_size():
            raise ValueError("state size mismatch")
        self.state = list(other.state)
        self.change_baseline = other.change_baseline
        self.last_delta = other.last_delta
        self.age = other.age
        return self

    # ---- behavior_ends
    def behavior_ends(self):
        """The ends that stand for what the Life did, as they stand."""
        b = self._behavior_base()
        return tuple(range(b, b + self.behavior_count))

    # ---- behavior_now
    def behavior_now(self):
        """What the behaviour ends are carrying right now, read as it is."""
        return list(self.bh_now)

    # ---- carries
    def carries(self, i, owner=LIFE):
        """Is this participant in this structure, and through which ports."""
        owners, ports = self.st_participants(i)
        if owner not in owners:
            return []
        return ports

    # ---- carry_state
    def carry_state(self):
        """The permanent address space beside what this moment is carrying.

        A reading, and nothing else: it decides nothing and writes nothing.  It
        is what the guard and the long run read instead of walking the whole
        address space to count the zeroes.
        """
        r = self.frame_now
        if isinstance(r, Carry):
            alive = r.taking()
            return {"width": len(r), "carrying": alive,
                    "carried": dict(r.carried()),
                    "zeros": len(r) - len(alive)}
        vals = list(r) if r else []
        return {"width": len(vals), "carrying": [u for u, v in enumerate(vals)
                                                 if v != ZERO],
                "carried": dict((u, v) for u, v in enumerate(vals)
                                if v != ZERO),
                "zeros": sum(1 for v in vals if v == ZERO)}

    # ---- carry_written
    def carry_written(self):
        """The addresses written into the one list on the last moment."""
        return tuple(sorted(self.walk_wrote))

    # ---- clear_activity_and_tissue
    def clear_activity_and_tissue(self):
        n = self.dna.state_size
        self.state = [0.0] * n
        self.change_baseline = 0.0
        self.last_delta = 0.0
        self.last_drive = [0.0] * n
        self.age = 0
        self.tissue = [0.0] * n
        self.tissue_baseline = [1.0 / n] * n
        self.latent_activity = [0.0] * self.dna.latent_count
        return self

    # ---- clone
    def clone(self):
        return self.from_life19(self, memory_enabled=self.memory_enabled,
                                structure_enabled=self.structure_enabled)

    # ---- _clone_step1
    def _clone_step1(self):
        other = LifeGrowth(self._base_dna, self.inlet,
                             memory_enabled=self.memory_enabled)
        for k, v in vars(self).items():
            if k in ("dna", "inlet", "_base_dna") or k in RETIRED_FIELDS:
                continue
            setattr(other, k, copy.deepcopy(v))
        other.dna = self.dna
        other._mem_index_build()
        return other

    # ---- _clone_step2
    def _clone_step2(self):
        other = LifeGrowth(self._base_dna, self.inlet,
                             memory_enabled=self.memory_enabled)
        for k, v in vars(self).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            setattr(other, k, copy.deepcopy(v))
        return other

    # ---- _clone_step3
    def _clone_step3(self):
        other = LifeGrowth(self._base_dna, self.inlet)
        for k, v in vars(self).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            setattr(other, k, copy.deepcopy(v))
        return other

    # ---- _clone_step4
    def _clone_step4(self):
        other = LifeGrowth(self._base_dna, self.inlet)
        for k, v in vars(self).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            setattr(other, k, copy.deepcopy(v))
        return other

    # ---- _clone_step5
    def _clone_step5(self):
        other = LifeGrowth(self._base_dna, self.inlet)
        for k, v in vars(self).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            setattr(other, k, copy.deepcopy(v))
        return other

    # ---- _clone_step6
    def _clone_step6(self):
        other = LifeGrowth(self._base_dna, self.inlet)
        for k, v in vars(self).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            setattr(other, k, copy.deepcopy(v))
        return other

    # ---- _clone_step7
    def _clone_step7(self):
        import copy
        other = LifeGrowth(self._base_dna, self.inlet)
        for k, v in vars(self).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            setattr(other, k, copy.deepcopy(v))
        other.dna = SourceEntryProxy(self._base_dna, other)
        return other

    # ---- _clone_step8
    def _clone_step8(self):
        tmp = self._clone_step9()
        other = LifeGrowth(self.dna, self.inlet)
        for k, v in vars(tmp).items():
            if k in ("dna", "inlet"):
                continue
            setattr(other, k, v)
        other.experience_flow = list(self.experience_flow)
        other.last_cue = list(self.last_cue)
        return other

    # ---- _clone_step9
    def _clone_step9(self):
        other = LifeGrowth(self.dna, self.inlet)
        other.state = list(self.state)
        other.change_baseline = self.change_baseline
        other.last_delta = self.last_delta
        other.last_drive = list(self.last_drive)
        other.age = self.age
        other.tissue = list(self.tissue)
        other.tissue_baseline = list(self.tissue_baseline)
        other.tissue_enabled = self.tissue_enabled
        other.latent_activity = list(self.latent_activity)
        other.coupling = [list(row) for row in self.coupling]
        other.growth_enabled = self.growth_enabled
        other.trace_keys = [list(k) for k in self.trace_keys]
        other.trace_cont = [list(c) for c in self.trace_cont]
        other.trace_born = list(self.trace_born)
        other.trace_used = list(self.trace_used)
        other.trace_enabled = self.trace_enabled
        other.trace_formation_enabled = self.trace_formation_enabled
        other.trace_shaping_enabled = self.trace_shaping_enabled
        other.trace_injection_on = self.trace_injection_on
        other.last_trace_age = self.last_trace_age
        return other

    # ---- _clone_step10
    def _clone_step10(self):
        other = LifeGrowth(self.dna, self.inlet)
        other.state = list(self.state)
        other.change_baseline = self.change_baseline
        other.last_delta = self.last_delta
        other.last_drive = list(self.last_drive)
        other.age = self.age
        other.tissue = list(self.tissue)
        other.tissue_baseline = list(self.tissue_baseline)
        other.tissue_enabled = self.tissue_enabled
        other.latent_activity = list(self.latent_activity)
        other.coupling = [list(row) for row in self.coupling]
        other.growth_enabled = self.growth_enabled
        return other

    # ---- _clone_step11
    def _clone_step11(self):
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

    # ---- _clone_step12
    def _clone_step12(self):
        other = Life(self.dna, self.inlet)
        other.state = list(self.state)
        other.change_baseline = self.change_baseline
        other.last_delta = self.last_delta
        other.last_drive = list(self.last_drive)
        other.age = self.age
        return other

    # ---- cn_label
    def cn_label(self, k):
        """This Connection, written the way the stage asks for it."""
        pre, post = self.cn_pre[k], self.cn_post[k]
        a = self.end_name(pre)
        b = self.end_name(post)
        pa = self.ow_owner.get(pre)
        pb = self.ow_owner.get(post)
        if pa is not None:
            a = "%s --[%s]--> " % (pa, self.end_name(pre))
        if pb is not None:
            b = " --[%s]--> %s" % (self.end_name(post), pb)
        return "%s%s" % (a, b)

    # ---- cn_owner
    def cn_owner(self, k):
        """Which two participants this Connection is between."""
        return (self.who(self.cn_pre[k]), self.who(self.cn_post[k]))

    # ---- cn_port
    def cn_port(self, k):
        """The ports that carried this Connection: (side, owner, end) rows.

        A Connection whose ends are ordinary ends has none, and that is kept as
        none rather than filled in with something made up.
        """
        out = []
        for side, u in ((0, self.cn_pre[k]), (1, self.cn_post[k])):
            o = self.ow_owner.get(u)
            if o is not None:
                out.append((side, o, u))
        return out

    # ---- cognition_state
    def cognition_state(self):
        st = self._cognition_state_step1()
        if self.past_run_enabled:
            st["past_runs"] = self.past_run_view()
        return st

    # ---- _cognition_state_step1
    def _cognition_state_step1(self):
        st = self._cognition_state_step2()
        st["way_origin_runs"] = self.sf_run_view()
        return st

    # ---- _cognition_state_step2
    def _cognition_state_step2(self):
        st = self._cognition_state_step3()
        st["run_history"] = self.run_history_view()
        return st

    # ---- _cognition_state_step3
    def _cognition_state_step3(self):
        st = self._cognition_state_step4()
        if self._self_unit() >= 0:
            st["self_perception"] = self.self_perception_view()
        return st

    # ---- _cognition_state_step4
    def _cognition_state_step4(self):
        st = self._cognition_state_step5()
        if self.structure_action_enabled:
            st["structure_action"] = self.structure_action_view()
        return st

    # ---- _cognition_state_step5
    def _cognition_state_step5(self):
        st = self._cognition_state_step6()
        if self.msiu_enabled:
            st["msiu"] = self.msiu_view()
        return st

    # ---- _cognition_state_step6
    def _cognition_state_step6(self):
        st = self._cognition_state_step7()
        if self.msiu_las_view_enabled:
            st["las"] = self.las_view_on_needs()
            st["las_around_the_needs"] = self.las_around_needs()
        return st

    # ---- _cognition_state_step7
    def _cognition_state_step7(self):
        st = self._cognition_state_step8()
        if self.msiu_view_enabled:
            st["rebuilt"] = self.msiu_state_view()
            st["structures_asking_for_change"] = self.structures_with_rebuilding()
        return st

    # ---- _cognition_state_step8
    def _cognition_state_step8(self):
        st = self._cognition_state_step9()
        ch = self._channels()
        st["ends"] = {
            "count": self.participants(),
            "from_reality": ch,
            "from_structures": len(self.st_ids),
            "names": ["ch%d" % u if u < ch else "s%d" % (u - ch)
                      for u in range(ch + len(self.st_ids))],
            "forms_now": [round(v, 9) for v in self.st_form],
            "take_part_moments": self.take_part_moments,
            "take_part_skipped": self.take_part_skipped,
        }
        return st

    # ---- _cognition_state_step9
    def _cognition_state_step9(self):
        st = self._cognition_state_step10()
        if self.las_enabled:
            st["las"] = self.las_view()
        return st

    # ---- _cognition_state_step10
    def _cognition_state_step10(self):
        st = self._cognition_state_step11()
        st["states"] = self.state_summary()
        st["state_changes"] = self.sf_changes
        st["state_moments"] = self.sf_moments
        st["moments_before_a_formed_way"] = self.sf_never
        return st

    # ---- _cognition_state_step11
    def _cognition_state_step11(self):
        st = self._cognition_state_step12()
        st["steps_fed"] = self.cog_steps
        st["steps_no_reality"] = self.cog_skipped
        return st

    # ---- _cognition_state_step12
    def _cognition_state_step12(self):
        st = self._cognition_state_step13()
        st["structures"] = [{
            "id": i,
            "ends": list(self.st_ends[i]),
            "edges": ["end%d->end%d" % e for e in self.st_edges[i]],
            "born": self.st_born[i],
            "frames": self.st_frames[i],
        } for i in range(len(self.st_ids))]
        st["structures_issued"] = len(self.st_ids)
        st["edges_now"] = ["end%d->end%d" % e for e in self.st_now_edges]
        return st

    # ---- _cognition_state_step13
    def _cognition_state_step13(self):
        return {
            "channels": (len(self.frame_now) if self.frame_now else 0),
            "connections": [{
                "id": k, "pre": self.cn_pre[k], "post": self.cn_post[k],
                "born": self.cn_born[k],
                "live": round(self.cn_live[k], 6),
                "peak": round(self.cn_peak[k], 6),
                "form": round(self.cn_form[k], 4),
            } for k in range(len(self.cn_pre))],
            "evidence_now": {"ch%d->ch%d" % key: round(v, 6)
                             for key, v in sorted(self.cn_now.items())},
            "best_never_formed": {"ch%d->ch%d" % key: round(v, 6)
                                  for key, v in sorted(self.cn_best_full.items())
                                  if key not in self.cn_index},
            "best_ever_including_early": {"ch%d->ch%d" % key: round(v, 6)
                                          for key, v in sorted(self.cn_best.items())},
            "ends": [{
                "id": i,
                "members": list(self.el_ends[i]),
                "acts": 0 in self.el_sides[i],
                "is_acted_on": 1 in self.el_sides[i],
                "born": self.el_born[i], "frames": self.el_frames[i],
            } for i in range(len(self.el_ends))],
            "ends_issued": self.el_issued,
            "ends_grew": self.el_grew,
        }

    # ---- conscious_state
    def conscious_state(self):
        return {"ticks": self.conscious_ticks, "active": self.conscious_active,
                "conscious_flow": list(self.conscious_flow),
                "cf_norm": math.sqrt(sum(v * v for v in self.conscious_flow))}

    # ---- conscious_step
    def conscious_step(self):
        dna = self._base_dna
        s = self.state
        n = len(s)
        m = dna.latent_count
        rho = dna.latent_rate
        eta, gamma, kappa = dna.eta, dna.gamma, dna.kappa
        inj = dna.injection

        zero = [0.0] * dna.channel_count
        real_drive = list(self.dna.entry_drive(zero))

        internal = dna.internal_coupling(s)
        mode = self.running_mode()
        a_new = [(1.0 - rho) * self.latent_activity[j] + rho * math.tanh(0.0)
                 for j in range(m)]

        feedback = [0.0] * n
        A = self.coupling
        for j in range(m):
            aj = a_new[j]
            if aj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                feedback[i] += row[i] * aj

        th_feedback = [0.0] * n
        if self.thought_enabled:
            T = self.thought_coupling
            for j in range(m):
                aj = a_new[j]
                if aj == 0.0:
                    continue
                row = T[j]
                for i in range(n):
                    th_feedback[i] += row[i] * aj
        inv_m = 1.0 / m
        total_fb = [feedback[i] + th_feedback[i] for i in range(n)]

        if self.trace_enabled and self.trace_injection_on and dna.trace_gain > 0.0:
            trace_in_old, _w, _g = self.touch_traces(self.conscious_flow)
            self.last_trace_in_old = list(trace_in_old)
            if self.internal_trace_weighting:
                trace_in = self.internal_trace_injection()
            else:
                trace_in = list(trace_in_old)
                self.last_internal_trace_in = list(trace_in_old)
            mu = dna.trace_gain
        else:
            trace_in = [0.0] * n
            self.last_internal_trace_in = [0.0] * n
            self.last_trace_in_old = [0.0] * n
            mu = 0.0

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = (real_drive[i] + kappa * internal[i] + inj * total_fb[i] * inv_m
                     + mu * trace_in[i])
            drive_out[i] = drive
            new_state[i] = s[i] + eta * (math.tanh(drive) - gamma * mode[i] * s[i])

        acc = 0.0
        for i in range(n):
            diff = new_state[i] - s[i]
            acc += diff * diff
        delta = math.sqrt(acc)

        d_internal = [new_state[i] - s[i] for i in range(n)]
        self.conscious_flow = [(1.0 - rho) * self.conscious_flow[i] + rho * d_internal[i]
                               for i in range(n)]

        if self.thought_enabled and self.thought_growing:
            self._grow_thought(a_new, s)

        self.state = new_state
        self.last_drive = drive_out
        self.last_delta = delta
        self.latent_activity = a_new
        self.conscious_ticks += 1

        self.last_conscious_drive = drive_out
        self.last_conscious_real_drive = real_drive
        self.last_conscious_feedback = feedback
        self.last_conscious_mode = mode
        self.last_conscious_internal = internal
        self.last_conscious_trace_in = trace_in
        self.last_conscious_d_internal = d_internal
        self.last_conscious_delta = delta

        self.last_thought_feedback = th_feedback
        self.last_thought_feedback_norm = math.sqrt(sum(v * v for v in th_feedback))
        self.last_thought_norm = self.thought_norm()

        return {"conscious_tick": self.conscious_ticks, "delta": delta,
                "external_input": 0.0, "trace_fired": self.last_trace_fired,
                "thought_norm": self.last_thought_norm,
                "thought_feedback_norm": self.last_thought_feedback_norm,
                "thought_growing": self.thought_growing,
                "age": self.age}

    # ---- _conscious_step_step1
    def _conscious_step_step1(self):
        dna = self._base_dna
        s = self.state
        n = len(s)
        m = dna.latent_count
        rho = dna.latent_rate
        eta, gamma, kappa = dna.eta, dna.gamma, dna.kappa
        inj = dna.injection

        zero = [0.0] * dna.channel_count
        real_drive = list(self.dna.entry_drive(zero))

        internal = dna.internal_coupling(s)
        mode = self.running_mode()
        a_new = [(1.0 - rho) * self.latent_activity[j] + rho * math.tanh(0.0)
                 for j in range(m)]

        feedback = [0.0] * n
        A = self.coupling
        for j in range(m):
            aj = a_new[j]
            if aj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                feedback[i] += row[i] * aj

        th_feedback = [0.0] * n
        if self.thought_enabled:
            T = self.thought_coupling
            for j in range(m):
                aj = a_new[j]
                if aj == 0.0:
                    continue
                row = T[j]
                for i in range(n):
                    th_feedback[i] += row[i] * aj
        inv_m = 1.0 / m
        total_fb = [feedback[i] + th_feedback[i] for i in range(n)]

        if self.trace_enabled and self.trace_injection_on and dna.trace_gain > 0.0:
            trace_in_old, _w, _g = self.touch_traces(self.conscious_flow)
            self.last_trace_in_old = list(trace_in_old)
            if self.internal_trace_weighting:
                trace_in = self.internal_trace_injection()
            else:
                trace_in = list(trace_in_old)
                self.last_internal_trace_in = list(trace_in_old)
            mu = dna.trace_gain
        else:
            trace_in = [0.0] * n
            self.last_internal_trace_in = [0.0] * n
            self.last_trace_in_old = [0.0] * n
            mu = 0.0

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = (real_drive[i] + kappa * internal[i] + inj * total_fb[i] * inv_m
                     + mu * trace_in[i])
            drive_out[i] = drive
            new_state[i] = s[i] + eta * (math.tanh(drive) - gamma * mode[i] * s[i])

        acc = 0.0
        for i in range(n):
            diff = new_state[i] - s[i]
            acc += diff * diff
        delta = math.sqrt(acc)

        d_internal = [new_state[i] - s[i] for i in range(n)]
        self.conscious_flow = [(1.0 - rho) * self.conscious_flow[i] + rho * d_internal[i]
                               for i in range(n)]

        if self.thought_enabled:
            self._grow_thought(a_new, s)

        self.state = new_state
        self.last_drive = drive_out
        self.last_delta = delta
        self.latent_activity = a_new
        self.conscious_ticks += 1

        self.last_conscious_drive = drive_out
        self.last_conscious_real_drive = real_drive
        self.last_conscious_feedback = feedback
        self.last_conscious_mode = mode
        self.last_conscious_internal = internal
        self.last_conscious_trace_in = trace_in
        self.last_conscious_d_internal = d_internal
        self.last_conscious_delta = delta

        self.last_thought_feedback = th_feedback
        self.last_thought_feedback_norm = math.sqrt(sum(v * v for v in th_feedback))
        self.last_thought_norm = self.thought_norm()

        return {"conscious_tick": self.conscious_ticks, "delta": delta,
                "external_input": 0.0, "trace_fired": self.last_trace_fired,
                "thought_norm": self.last_thought_norm,
                "thought_feedback_norm": self.last_thought_feedback_norm,
                "age": self.age}

    # ---- _conscious_step_step2
    def _conscious_step_step2(self):
        dna = self._base_dna
        s = self.state
        n = len(s)
        m = dna.latent_count
        rho = dna.latent_rate
        eta, gamma, kappa = dna.eta, dna.gamma, dna.kappa
        inj = dna.injection

        zero = [0.0] * dna.channel_count
        real_drive = list(self.dna.entry_drive(zero))

        internal = dna.internal_coupling(s)
        mode = self.running_mode()
        a_new = [(1.0 - rho) * self.latent_activity[j] + rho * math.tanh(0.0)
                 for j in range(m)]

        feedback = [0.0] * n
        A = self.coupling
        for j in range(m):
            aj = a_new[j]
            if aj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                feedback[i] += row[i] * aj

        th_feedback = [0.0] * n
        if self.thought_enabled:
            T = self.thought_coupling
            for j in range(m):
                aj = a_new[j]
                if aj == 0.0:
                    continue
                row = T[j]
                for i in range(n):
                    th_feedback[i] += row[i] * aj
        inv_m = 1.0 / m
        total_fb = [feedback[i] + th_feedback[i] for i in range(n)]

        if self.trace_enabled and self.trace_injection_on and dna.trace_gain > 0.0:
            trace_in, _w, _g = self.touch_traces(self.conscious_flow)
            mu = dna.trace_gain
        else:
            trace_in, _w, _g = [0.0] * n, [], []
            mu = 0.0

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = (real_drive[i] + kappa * internal[i] + inj * total_fb[i] * inv_m
                     + mu * trace_in[i])
            drive_out[i] = drive
            new_state[i] = s[i] + eta * (math.tanh(drive) - gamma * mode[i] * s[i])

        acc = 0.0
        for i in range(n):
            diff = new_state[i] - s[i]
            acc += diff * diff
        delta = math.sqrt(acc)

        d_internal = [new_state[i] - s[i] for i in range(n)]
        self.conscious_flow = [(1.0 - rho) * self.conscious_flow[i] + rho * d_internal[i]
                               for i in range(n)]

        if self.thought_enabled:
            self._grow_thought(a_new, s)

        self.state = new_state
        self.last_drive = drive_out
        self.last_delta = delta
        self.latent_activity = a_new
        self.conscious_ticks += 1

        self.last_conscious_drive = drive_out
        self.last_conscious_real_drive = real_drive
        self.last_conscious_feedback = feedback
        self.last_conscious_mode = mode
        self.last_conscious_internal = internal
        self.last_conscious_trace_in = trace_in
        self.last_conscious_d_internal = d_internal
        self.last_conscious_delta = delta

        self.last_thought_feedback = th_feedback
        self.last_thought_feedback_norm = math.sqrt(sum(v * v for v in th_feedback))
        self.last_thought_norm = self.thought_norm()

        return {"conscious_tick": self.conscious_ticks, "delta": delta,
                "external_input": 0.0, "trace_fired": self.last_trace_fired,
                "thought_norm": self.last_thought_norm,
                "thought_feedback_norm": self.last_thought_feedback_norm,
                "age": self.age}

    # ---- _conscious_step_step3
    def _conscious_step_step3(self):
        dna = self._base_dna
        s = self.state
        n = len(s)
        m = dna.latent_count
        rho = dna.latent_rate
        eta, gamma, kappa = dna.eta, dna.gamma, dna.kappa
        inj = dna.injection

        zero = [0.0] * dna.channel_count
        real_drive = list(self.dna.entry_drive(zero))

        internal = dna.internal_coupling(s)
        mode = self.running_mode()

        a_new = [(1.0 - rho) * self.latent_activity[j] + rho * math.tanh(0.0)
                 for j in range(m)]

        feedback = [0.0] * n
        A = self.coupling
        for j in range(m):
            aj = a_new[j]
            if aj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                feedback[i] += row[i] * aj
        inv_m = 1.0 / m

        if self.trace_enabled and self.trace_injection_on and dna.trace_gain > 0.0:
            trace_in, _w, _g = self.touch_traces(self.conscious_flow)
            mu = dna.trace_gain
        else:
            trace_in, _w, _g = [0.0] * n, [], []
            mu = 0.0

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = (real_drive[i] + kappa * internal[i] + inj * feedback[i] * inv_m
                     + mu * trace_in[i])
            drive_out[i] = drive
            new_state[i] = s[i] + eta * (math.tanh(drive) - gamma * mode[i] * s[i])

        acc = 0.0
        for i in range(n):
            diff = new_state[i] - s[i]
            acc += diff * diff
        delta = math.sqrt(acc)

        d_internal = [new_state[i] - s[i] for i in range(n)]
        self.conscious_flow = [(1.0 - rho) * self.conscious_flow[i] + rho * d_internal[i]
                               for i in range(n)]

        self.state = new_state
        self.last_drive = drive_out
        self.last_delta = delta
        self.latent_activity = a_new
        self.conscious_ticks += 1

        self.last_conscious_drive = drive_out
        self.last_conscious_real_drive = real_drive
        self.last_conscious_feedback = feedback
        self.last_conscious_mode = mode
        self.last_conscious_internal = internal
        self.last_conscious_trace_in = trace_in
        self.last_conscious_d_internal = d_internal
        self.last_conscious_delta = delta

        return {"conscious_tick": self.conscious_ticks, "delta": delta,
                "external_input": 0.0, "trace_fired": self.last_trace_fired,
                "age": self.age}

    # ---- coupling_flat
    def coupling_flat(self):
        return [v for row in self.coupling for v in row]

    # ---- coupling_norm
    def coupling_norm(self):
        return math.sqrt(sum(v * v for row in self.coupling for v in row))

    # ---- coupling_row_norms
    def coupling_row_norms(self):
        return [math.sqrt(sum(v * v for v in row)) for row in self.coupling]

    # ---- el_participants
    def el_participants(self, e):
        """Which participants an element is made of, and through which ports.

        Read off `el_ends`, the base's own table of what each element holds.  A
        port is read as its owner with the port kept beside it: the Life is in
        the element once, however many of its ports stand there.
        """
        owners, ports = [], []
        for u in self.el_ends[e]:
            o = self.who(u)
            if o not in owners:
                owners.append(o)
            if self.is_port(u) and u not in ports:
                ports.append(u)
        return owners, sorted(ports)

    # ---- element_reach
    def element_reach(self, e):
        """The channels, and the Life, an element is really on.

        A unit is a channel, the Life, or a Structure, so the leaves are read the
        same way at every level.  The Life unit is a leaf of this reading, the
        way a channel is: it is not made of anything, and nothing stands for it.
        """
        base = self._base_units()
        out, stack, seen = [], list(self.el_ends[e]), set()
        while stack:
            u = stack.pop()
            if u < base:
                if u not in out:
                    out.append(u)
                continue
            j = self.structure_of_unit(u)
            if j < 0 or j in seen:
                continue
            seen.add(j)
            for e2 in self.st_ends[j]:
                stack.extend(list(self.el_ends[e2]))
        return out

    # ---- _element_reach_step1
    def _element_reach_step1(self, e):
        """The channels an element is really on, down through what it is made of.

        An element is made of units and a unit is a channel or a Structure, so
        the channels are read the same way at every level: a Structure's channels
        are the channels of its elements.  Nothing is declared and nothing is
        assumed -- it is read off el_ends, the base's own table of what each
        element is made of.
        """
        ch = self._channels()
        out, stack, seen = [], list(self.el_ends[e]), set()
        while stack:
            u = stack.pop()
            if u < ch:
                if u not in out:
                    out.append(u)
                continue
            j = self.structure_of_unit(u)
            if j < 0 or j in seen:
                continue
            seen.add(j)
            for e2 in self.st_ends[j]:
                stack.extend(list(self.el_ends[e2]))
        return out

    # ---- end_label
    def end_label(self, u):
        """A short name for any place in the one list, for the readings only."""
        w = self.word_at(u)
        if w is not None:
            return "form'%s'" % w
        ch = self._channels()
        if 0 <= u < ch:
            return "world%d" % u
        beh = list(self.behavior_ends())
        if u in beh:
            return "behaviour%d" % beh.index(u)
        if u == self._self_unit():
            return "LIFE"
        j = self.structure_of_unit(u)
        if j >= 0:
            return "structure#%d" % j
        e = self.run_of_unit(u)
        if e >= 0:
            return "run#%d" % e
        return "end%d" % u

    # ---- end_name
    def end_name(self, unit):
        """What an end is, in words, read off the base's own place tables."""
        ch = self._channels()
        beh = list(self.behavior_ends())
        if 0 <= unit < ch:
            return "world channel %d" % unit
        if unit in beh:
            return "behaviour%d" % beh.index(unit)
        if unit == self._self_unit():
            return "unit 12 (the old Life cell, not this identity)"
        j = self.structure_of_unit(unit)
        if j >= 0:
            return "structure #%d's slot" % j
        e = self.run_of_unit(unit)
        if e >= 0:
            return "run #%d's slot" % e
        return "end %d" % unit

    # ---- enter_consciousness
    def enter_consciousness(self):
        cf = self._enter_consciousness_step1()
        self.thought_growing = True
        self.thought_finished_at = None
        return cf

    # ---- _enter_consciousness_step1
    def _enter_consciousness_step1(self):
        cf = self._enter_consciousness_step2()
        n = self._base_dna.state_size
        m = self._base_dna.latent_count
        self.thought_coupling = [[0.0] * n for _ in range(m)]
        self.thought_updates = 0
        self.last_thought_feedback = [0.0] * n
        self.last_thought_feedback_norm = 0.0
        self.last_thought_norm = 0.0
        return cf

    # ---- _enter_consciousness_step2
    def _enter_consciousness_step2(self):
        self.conscious_flow = list(self.experience_flow)
        self.conscious_ticks = 0
        self.conscious_active = True
        self._frame_source = [0.0] * self.source_dim
        return list(self.conscious_flow)

    # ---- express
    def express(self, top=1, margin=None):
        """What the Life says, translated out of the organisation standing now.

        The organ does not decide what the Life wants to say, and it brings no
        sequence of its own.  It reads the organisation that is standing this
        moment and writes it out in human forms: the order comes from the
        Structure's **own inner Connections** (`st_edges`, a walk over them),
        and the form each place stands for comes from the organ's own table,
        which holds only what the Life has really met (`word_at`).

        Human language is a translation here, not the Life's own tongue: the
        Life's own tongue is the Connections it is made of.

        A Structure that holds no form says nothing.  If more than one is
        standing, the first one that holds forms is read; nothing is ranked,
        completed, permuted or made up, and no sequence is kept anywhere.
        """
        if not self.expression_enabled:
            return []
        for i in self.cur_st:
            if not (0 <= i < len(self.st_ids)):
                continue
            said = []
            for u in self._organ_order(i):
                name = self._say_name(u)
                if name is not None and name not in said:
                    said.append(name)
            if said:
                self.expression_expressed += 1
                return [(n, 1.0) for n in said]
        return []

    # ---- _say_name   (this file's own: the organ's own naming)
    def _say_name(self, u):
        """The human form one place stands for, or None.

        This is the organ's own table and nothing else: it holds only what has
        really been met (`word_at`).  Human language is a translation here, so
        an organ that reads a different surface overrides this and nothing else
        -- the order of what is said is not the organ's business.
        """
        return self.word_at(u)

    # ---- _organ_order   (this file's own)
    def _organ_order(self, i):
        """The places a Structure holds, in the order of its own Connections.

        Read off the Structure's frozen tables: `st_edges` is its own inner
        organisation, at the level of the Elements it is made of, and the
        places are the ones that are members of those Elements.  A walk over
        its own edges gives the order -- an Element nothing acts on is walked
        first, and anything the walk never reaches follows the walk, so no
        place is lost and no place is invented.

        The organ does not order them, does not complete them, and keeps no
        sequence: the order is the Structure's own, read as it stands.
        """
        edges = list(self.st_edges[i])
        ends = [int(e) for e in self.st_ends[i]]
        nxt, has_in = {}, set()
        for a, b in edges:
            nxt.setdefault(int(a), []).append(int(b))
            has_in.add(int(b))
        order, seen = [], set()

        def walk(e):
            if e in seen:
                return
            seen.add(e)
            order.append(e)
            for m in sorted(nxt.get(e, ())):
                walk(m)

        for e in ends:
            if e not in has_in:
                walk(e)
        for e in ends:
            walk(e)
        out = []
        for e in order:
            if not (0 <= e < len(self.el_ends)):
                continue
            for u in sorted(self.el_ends[e]):
                if u not in out:
                    out.append(u)
        return out

    # ---- _express_step1
    def _express_step1(self, top=1, margin=None):
        """Let an action out, and read it back as a form that was really met.

        It can only choose among the forms it has met; it never makes one up, and
        it does not complete, reason or organise anything.  Candidates are taken
        by how close they are to the action -- not by how often they were met.
        """
        if not self.expression_enabled or not self.expression_forms:
            return []
        act = self.action()
        if _norm(act) <= 1e-12:
            return []
        if margin is None:
            margin = FORM_MARGIN
        scored = [(_cos(act, e[0]), self.expression_first[f], f)
                  for f, e in self.expression_forms.items()]
        best = max(s[0] for s in scored)
        cand = [s for s in scored if s[0] >= best - margin]
        cand.sort(key=lambda x: (-x[0], x[1]))   # closeness; ties by first met
        out = [(f, g) for g, _o, f in cand]
        self.expression_expressed += 1
        return out[:top] if top else out

    # ---- expression_memory
    def expression_memory(self):
        """What the organ really learned, ready to be written down.

        Only experience: which forms were met, what the Life itself was letting
        out when each was met, how often, and the order they were first met in.
        """
        return {
            "forms_met": self.expression_met,
            "asked": self.expression_expressed,
            "first": {f: int(i) for f, i in self.expression_first.items()},
            "forms": {f: [list(e[0]), float(e[1])]
                      for f, e in self.expression_forms.items()},
            "acts": {f: [list(v) for v in vs]
                     for f, vs in self.expression_acts.items()},
        }

    # ---- expression_restore
    def expression_restore(self, d):
        """Take the organ's experience back, on top of nothing.

        What comes back is what was met before -- not a fresh start and not a
        template.  A form that was never met is still not held, and the order
        each was first met in is the order it really was first met in.
        """
        self.expression_forms = {}
        self.expression_acts = {}
        self.expression_first = {}
        for f, e in (d.get("forms") or {}).items():
            self.expression_forms[f] = [list(e[0]), float(e[1])]
        for f, i in (d.get("first") or {}).items():
            self.expression_first[f] = int(i)
        for f, vs in (d.get("acts") or {}).items():
            self.expression_acts[f] = [list(v) for v in vs]
        # a state file written before the experiences were kept carries one
        # averaged vector per form; that one meeting is what it really had, so
        # it is taken as the experience it stands for -- nothing is invented
        for f, e in self.expression_forms.items():
            if f not in self.expression_acts:
                self.expression_acts[f] = [list(e[0])]
        self.expression_met = int(d.get("forms_met", 0))
        self.expression_expressed = int(d.get("asked", 0))

    # ---- expression_state
    def expression_state(self):
        return {
            "enabled": self.expression_enabled,
            "forms_met": len(self.expression_forms),
            "forms_really_met": self.expression_met,
            "asked": self.expression_expressed,
            "has_thinking_result": self.thought_has_result(),
            "thought_norm": round(self.thought_norm(), 9),
            "action": [round(v, 9) for v in self.action()],
            "action_norm": round(_norm(self.action()), 9),
        }

    # ---- feedback_of
    def feedback_of(self, s=None):
        if s is None:
            s = self.state
        n = self.dna.state_size
        m = self.dna.latent_count
        out = [0.0] * n
        for j in range(m):
            aj = self.latent_activity[j]
            if aj == 0.0:
                continue
            row = self.coupling[j]
            for i in range(n):
                out[i] += row[i] * aj
        return [v / m for v in out]

    # ---- finish_thinking
    def finish_thinking(self):
        self.thought_growing = False
        self.thought_finished_at = self.conscious_ticks
        return list(self.thought_coupling)

    # ---- form_now
    def form_now(self, name):
        """This form's place, the Element identity it belongs to, and whether that
        identity is taking part now -- by its own place, or through other members."""
        u = self.word_unit(name)
        self._align_now()
        out = {"unit": u, "cell": self.word_cell(name), "acting": False,
               "owner": -1, "owner_now": False, "owner_structures": [],
               "hist_ids": [], "hist_taking_part": []}
        if u < 0:
            return out
        out["hist_ids"] = [i for i, m in enumerate(self.el_ends) if u in m]
        out["owner"] = self.el_at.get(u, -1)
        out["acting"] = u in self.el_at
        out["owner_now"] = out["owner"] >= 0 and out["owner"] in set(self.cur_el)
        if out["owner"] >= 0:
            out["owner_structures"] = [i for i in self.cur_st
                                       if out["owner"] in self.st_ends[i]]
        out["hist_taking_part"] = [i for i in out["hist_ids"]
                                   if i in set(self.cur_el)]
        return out

    # ---- formed_now
    def formed_now(self):
        """The elements formed on this very moment, and the forms in them."""
        return list(self.sp_now)

    # ---- from_life
    @classmethod
    def from_life(cls, life, memory_enabled=True, structure_enabled=True):
        return cls.from_life19(life, memory_enabled=memory_enabled,
                               structure_enabled=structure_enabled)

    # ---- _from_life_step1
    @classmethod
    def _from_life_step1(cls, life, memory_enabled=True):
        return cls.from_life18(life, memory_enabled=memory_enabled)

    # ---- _from_life_step2
    @classmethod
    def _from_life_step2(cls, life, memory_enabled=True):
        other = cls(life._base_dna, life.inlet, memory_enabled=memory_enabled)
        for k, v in vars(life).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            setattr(other, k, copy.deepcopy(v))

        other.bar_d = [0.0] * other._base_dna.state_size
        other.mem_prev_u = None
        other.mem_inj_prev = None
        other.mem_last_u = None
        other.mem_coeff, other.mem_g_last = [], []
        other._mem_part_last, other._mem_part_now = {}, {}
        other.mem_active_touched = other.mem_active_computed = other.mem_active_fired = 0
        other.mem_active_fireable = 0
        other.mem_active_set = []
        other.mem_fired_last = ()
        other.mem_frames = other.mem_recognized = 0
        other._mem_have_input = False
        # the memory's own rows stand beside the Connections, so an emptied
        # memory is made to the Connections' own length rather than left short
        _mem_align(other, {})
        if other.memory_enabled:
            other._detach_old_trace_layer()
        return other

    # ---- from_life18
    @classmethod
    def from_life18(cls, life, memory_enabled=True):
        other = cls(life._base_dna, life.inlet, memory_enabled=memory_enabled)
        for k, v in vars(life).items():
            if k in ("dna", "inlet", "_base_dna") or k in RETIRED_FIELDS:
                continue
            setattr(other, k, copy.deepcopy(v))
        other.mem_floor = float(other._base_dna.trace_rate) ** 2
        other.mem_horizon = int(math.log(other.mem_floor) / math.log(1.0 - float(other._base_dna.trace_rate))) \
            if 0.0 < float(other._base_dna.trace_rate) < 1.0 else 0
        other.mem_prev_u = None
        other.mem_inj_prev = None
        other.mem_coeff, other.mem_g_last = {}, []
        other._mem_part_now = {}
        other._mem_have_input = False
        other.mem_front = []
        other.mem_active_set = []
        other.mem_active_front = 0
        other.mem_active_touched = other.mem_active_computed = 0
        other.mem_active_fireable = other.mem_active_fired = 0
        other.mem_fired_last = ()
        other.mem_last_recognized = -1
        other.mem_search_size = 0
        other.mem_flow_size = 0
        other.mem_frames = other.mem_recognized = 0
        other._mem_index_build()
        other._mem_front_seed()
        return other

    # ---- from_life19
    @classmethod
    def from_life19(cls, life, memory_enabled=True, structure_enabled=True):
        other = cls(life._base_dna, life.inlet, memory_enabled=memory_enabled,
                    structure_enabled=structure_enabled)
        for k, v in vars(life).items():
            if k in ("dna", "inlet", "_base_dna"):
                continue
            if hasattr(other, k) or k.startswith("str_"):
                setattr(other, k, copy.deepcopy(v))
        other.dna = life.dna
        other._mem_index_build()
        other._str_rebuild_index()
        return other

    # ---- init_words
    def init_words(self):
        """Start with no form at all: nothing is preset and nothing is expected."""
        self.wd_unit = {}        # a form -> its own place in the one list
        self.wd_order = []       # the order in which forms first really appeared
        self.wd_now = {}         # a form -> what it carries this moment (1 or 0)
        self.wd_shown = []       # the forms really in the world this moment
        self.wd_seen = {}        # a form -> the moments it has really appeared
        self.wd_pending = []     # forms that want a place, as this moment begins
        self.wd_born = {}        # a form -> the moment it first really appeared
        self.wd_moments = 0      # moments the world showed anything at all

    # ---- internal_trace_injection
    def internal_trace_injection(self):
        n = self._base_dna.state_size
        out = [0.0] * n
        internal_w = []
        gs = self.last_trace_g
        ws = self.last_trace_w
        for j, wj in enumerate(ws):
            gj = gs[j] if j < len(gs) else 0.0
            coeff = wj * max(gj, 0.0)
            internal_w.append(coeff)
            if coeff == 0.0:
                continue
            cont = self.trace_cont[j]
            for i in range(n):
                out[i] += coeff * cont[i]
        self.last_internal_trace_w = internal_w
        self.last_internal_trace_in = out
        return out

    # ---- internal_trace_state
    def internal_trace_state(self):
        return {"internal_w": list(self.last_internal_trace_w),
                "weighting": self.internal_trace_weighting,
                "g": list(self.last_trace_g), "w": list(self.last_trace_w)}

    # ---- is_port
    def is_port(self, unit):
        """Is this end a port of somebody other than itself?"""
        return unit in self.ow_owner

    # ---- las_around_needs
    def las_around_needs(self):
        """The whole around every Connection in a state now, and nothing else."""
        now = self.msiu_now()
        return {
            "rebuilding_now": [n["identity"] for n in now],
            "asked_about": len(now),
            "nothing_to_show_because_no_need_is_current": len(now) == 0,
            "for_each_current_rebuilding": [self.las_for_msiu(n) for n in now],
            "not_current_any_more": [
                n["identity"]
                for n in self.msiu_state_view()["not_current_any_more"]],
        }

    # ---- las_for_msiu
    def las_for_msiu(self, n):
        """The whole a Connection in a state points at, read off what the run holds.

        The record already carries the entry: `against_connection` is the actual
        connection whose state asked for a change, and `in_structure` is the
        Structure that connection was formed in.  Everything shown here is read
        from those two, at this moment, off tables that already exist.
        """
        n = self._ms_at(n)
        k = n["against_connection"]
        sid = n["in_structure"]
        has = 0 <= sid < len(self.st_ends)
        mem = tuple(self.st_ends[sid]) if has else ()
        inner = tuple(self.st_edges[sid]) if has else ()
        now_edges = set(self.st_now_edges)
        still_running = [e for e in inner if e in now_edges]
        not_running = [e for e in inner if e not in now_edges]
        conns = self._las_connections_of(mem) if has else [k]
        now = self.frame_now or []

        return {
            "the_connection": {
                "identity": n["identity"],
                "kind": n["kind"],
                "came_about": n["came_about"],
                "current": bool(n["current"]),
                "what_it_came_from": dict(n["from"]),
            },
            "the_connection": self._las_connection(k),
            "the_structure": {
                "identity": sid,
                "born": self.st_born[sid] if has else None,
                "ran_moments": self.st_frames[sid] if has else 0,
                "elements": self._las_elements(mem),
                "connections": [self._las_connection(c) for c in conns],
                "organisation_as_formed": ["e%d>e%d" % e for e in inner],
                "organisation_still_running": ["e%d>e%d" % e
                                               for e in still_running],
                "parts_of_the_organisation_not_running": ["e%d>e%d" % e
                                                          for e in not_running],
                "it_is_running_as_it_was_formed": not not_running,
                # which of its connections still really act, read off the same
                # bar the base already uses to call a connection running
                "connections_still_acting": [c for c in conns
                                             if self.cn_live[c] >= self._own_conn_bar()],
                "connections_not_acting": [c for c in conns
                                           if self.cn_live[c] < self._own_conn_bar()],
            },
            "the_reality_acting_on_it_now": {
                "the_channels_these_elements_are_read_on": {
                    "ch%d" % c: round(now[c], 6)
                    for e in mem for c in self.el_ends[e]} if now else {},
                "this_connection_acts_now": round(self.cn_live[k], 6),
                "the_way_it_acts_now": round(self.cn_form[k], 6)
                if self.cn_form[k] is not None else None,
                "the_way_it_was_formed_to_act": self.sf_way.get(k),
            },
        }

    # ---- las_lines
    def las_lines(self):
        """The same thing said out loud.  No wording of its own beyond readings."""
        v = self.las_view()
        sc = v["scope"]
        out = []
        out.append("what this Life currently holds: %d elements, %d connections, "
                   "%d structures established"
                   % (sc["elements_formed"], sc["connections_formed"],
                      sc["structures_established"]))
        if not v["structures"]:
            out.append("no structure has been established yet, so there is "
                       "nothing to show a connection's state against")
        for s in v["structures"]:
            out.append("")
            out.append("structure #%d   %d elements, %d connections"
                       % (s["identity"], len(s["elements"]), len(s["connections"])))
            out.append("   elements: %s"
                       % "; ".join("#%d (of %s)%s"
                                   % (e["identity"],
                                      ",".join("ch%d" % c for c in e["channels"]),
                                      ", still here" if e["in_reality_now"] else ", "
                                      "not seen now")
                                   for e in s["elements"]))
            out.append("   organisation as formed: %s"
                       % ("  ".join(s["organisation"]) or "(none)"))
            if s["running_as_formed"]:
                out.append("   it is running as it was formed (%d moments so far)"
                           % s["confirmed_moments"])
            else:
                out.append("   it is NOT running as it was formed: %s no longer "
                           "run (%d moments in all)"
                           % ("  ".join(s["parts_not_running_now"]),
                              s["confirmed_moments"]))
            out.append("   its connections: stable %s | mismatch %s | broken %s%s"
                       % (s["stable"] or "-", s["mismatch"] or "-",
                          s["broken"] or "-",
                          " | not judgeable yet %s" % s["unconfirmed"]
                          if s["unconfirmed"] else ""))
        if v["problem"]:
            out.append("")
            out.append("where the problem really is:")
            for p in v["problem"]:
                out.append("   connection #%d  %s  between element #%d and element "
                           "#%d  in structure #%s  -- it acts %.3f, its manner now "
                           "%s, the way it was formed %s"
                           % (p["connection"], p["state"], p["between"][0],
                              p["between"][1], p["structure"], p["acting_now"],
                              p["manner_now"], p["the_way_it_was_formed"]))
        else:
            out.append("")
            out.append("no connection is mismatched or broken: there is no problem "
                       "to show here")
        if v["unconfirmed"]:
            out.append("")
            out.append("cannot be confirmed from what is here:")
            for u in v["unconfirmed"][:12]:
                out.append("   connection #%d between element #%d and element #%d: %s"
                           % (u["connection"], u["between"][0], u["between"][1],
                              u["why"]))
        return out

    # ---- las_need_lines
    def las_need_lines(self):
        """Every Connection in a state, shown around the whole it points at."""
        v = self.las_around_needs()
        out = []
        if not v["asked_about"]:
            out.append("no Connection is in a state now, so there is "
                       "nothing for LAS to look at: no connection is "
                       "mismatched or broken")
            if v["not_current_any_more"]:
                out.append(" (%s came about earlier and are no longer "
                           "current; a Connection not in a state asks for "
                           "nothing)"
                           % v["not_current_any_more"])
            return out
        for s in v["for_each_current_rebuilding"]:
            out.extend(self._msiu_words(s))
            out.append("")
        out.append("this is the whole a Connection in a state points at, read as it is: "
                   "no element to connect, no connection to make, and no way of "
                   "making it is named here")
        return out

    # ---- las_view
    def las_view(self):
        """The current real structure, made only of what the Life itself holds."""
        edges_now = set(self.st_now_edges)
        view = {"scope": {}, "structures": [], "problem": [], "unconfirmed": []}
        attributed = set()
        for i in range(len(self.st_ids)):
            mem = tuple(self.st_ends[i])
            inner = tuple(self.st_edges[i])
            conns = self._las_connections_of(mem)
            attributed.update(conns)
            judged = [k for k in conns if k in self.sf_way]
            un = [k for k in conns if k not in self.sf_way]
            by = {STABLE: [], MISMATCH: [], BROKEN: []}
            for k in judged:
                by[self.sf_state[k]].append(k)
            missing = [e for e in inner if e not in edges_now]
            elements = []
            for e in mem:
                chans = list(self.el_ends[e])
                elements.append({
                    "identity": e, "channels": chans, "born": self.el_born[e],
                    "seen_moments": self.el_frames[e],
                    "in_reality_now": bool(self.frame_now) and any(
                        abs(self.frame_now[c]) > 0.0 for c in chans),
                })
            s = {
                "identity": i,
                "elements": elements,
                "connections": conns,
                "organisation": ["e%d>e%d" % e for e in inner],
                "organisation_running_now": ["e%d>e%d" % e for e in inner
                                             if e in edges_now],
                "parts_not_running_now": ["e%d>e%d" % e for e in missing],
                "running_as_formed": not missing,
                "confirmed_moments": self.st_frames[i],
                "born": self.st_born[i],
                "stable": by[STABLE], "mismatch": by[MISMATCH],
                "broken": by[BROKEN],
                "unconfirmed": un,
            }
            view["structures"].append(s)
            for k in by[MISMATCH] + by[BROKEN]:
                view["problem"].append({
                    "connection": k, "state": STATE_NAMES[self.sf_state[k]],
                    "between": [self._end_of_channel(self.cn_pre[k]),
                                self._end_of_channel(self.cn_post[k])],
                    "structure": i,
                    "the_way_it_was_formed": self.sf_way[k],
                    "acting_now": round(self.cn_live[k], 6),
                    "manner_now": round(self.cn_form[k], 6)
                    if self.cn_form[k] is not None else None,
                })
            for k in un:
                view["unconfirmed"].append({
                    "connection": k, "structure": i,
                    "between": [self._end_of_channel(self.cn_pre[k]),
                                self._end_of_channel(self.cn_post[k])],
                    "why": "no established way to compare it with yet",
                })
        # connections that belong to no established structure at all
        loose = [k for k in range(len(self.cn_pre)) if k not in attributed]
        for k in loose:
            view["unconfirmed"].append({
                "connection": k, "structure": None,
                "between": [self._end_of_channel(self.cn_pre[k]),
                            self._end_of_channel(self.cn_post[k])],
                "why": "no established structure holds it yet",
            })
        running = [s["identity"] for s in view["structures"] if s["running_as_formed"]]
        view["scope"] = {
            "structures_established": len(self.st_ids),
            "structures_running_as_formed": running,
            "connections_formed": len(self.cn_pre),
            "elements_formed": len(self.el_ends),
            "connections_judged": len(self.sf_way),
        }
        return view

    # ---- las_view_on_needs
    def las_view_on_needs(self):
        """'s view, plus what a state makes it look at."""
        v = self._las_view_step0()
        if self.msiu_las_view_enabled:
            v["around_the_needs"] = self.las_around_needs()
        return v

    # ---- life_unit_form
    def life_unit_form(self):
        """What the Life unit carries right now, read as it is."""
        return self.lf_form

    # ---- memory_state
    def memory_state(self, full_act=False):
        st = self._memory_state_step1(full_act=full_act)
        st["addressing"] = self._addr_state()
        return st

    # ---- _memory_state_step1
    def _memory_state_step1(self, full_act=False):
        st = self._memory_state_step2(full_act=full_act)
        return st

    # ---- _memory_state_step2
    def _memory_state_step2(self, full_act=False):
        hit = list(self.mem_hit)
        st = {"enabled": self.memory_enabled, "theta": self.mem_theta,
              "frames": self.mem_frames,
              "recognized": self.mem_recognized,
              "n_conn": len(self.cn_pre),
              "n_confirmed": sum(1 for h in hit if h > 0),
              "n_once_only": sum(1 for h in hit if h == 0),
              "born": len(self.cn_born),
              "hit": hit,
              "s": [round(x, 6) for x in self.mem_s],
              "born_at": list(self.cn_born),
              "bar_d_norm": _norm(self.bar_d), "last_g": self.mem_g_last,
              "front": {"size": self.mem_active_front, "floor": self.mem_floor,
                        "horizon": self.mem_horizon},
              "active": {"touched": self.mem_active_touched,
                         "computed": self.mem_active_computed,
                         "searched": self.mem_search_size,
                         "flowed": self.mem_flow_size,
                         "fireable": self.mem_active_fireable,
                         "fired": self.mem_active_fired,
                         "set": list(self.mem_active_set)}}
        if full_act:
            act = [self._mem_act_now(k) for k in range(len(self.mem_act))]
            st.update({"act": [round(x, 6) for x in act],
                       "act_mean": (sum(act) / len(act)) if act else 0.0,
                       "act_min": min(act) if act else 0.0,
                       "act_max": max(act) if act else 0.0,
                       "key_norm": [(round(_norm(k), 6) if k is not None else 0.0)
                                    for k in self.cn_key]})
        return st

    # ---- mouth_emit
    def mouth_emit(self, forms):
        """Hand the mouth what is taking part now, and it sends exactly that.

        It decides nothing: no action is read, no closeness is computed, no form
        is chosen, no reality's name is looked at.  An empty hand means silence.
        """
        got = sorted(set(forms))
        self.sp_asked += 1
        if not got:
            self.sp_silent += 1
            self.sp_sent.append((self.age, []))
            return []
        self.sp_sent.append((self.age, got))
        return got

    # ---- mouth_install
    def mouth_install(self, table):
        """Put a table of forms on the organ, in place of the one it has.

        Used for one reading only: the same behaviour, another Life's having
        met.  Nothing but the organ's own three quantities is written.
        """
        self.expression_forms = {f: [list(row), float(w)]
                                 for f, (row, w) in table["forms"].items()}
        self.expression_first = dict(table["first"])
        self.expression_met = int(table["met"])
        return len(self.expression_forms)

    # ---- mouth_lines
    def mouth_lines(self):
        out = ["the organ, as it stands: %d form(s) really met, asked %d time(s)"
               % (len(self.expression_forms), self.expression_expressed)]
        for f, (_row, w) in sorted(self.expression_forms.items(),
                                   key=lambda kv: self.expression_first[kv[0]]):
            out.append("  %r : arrived %d time(s)" % (f, int(w)))
        return out

    # ---- mouth_met
    def mouth_met(self):
        """Which forms it has really met, and how often each one arrived."""
        return {f: int(w) for f, (_row, w) in self.expression_forms.items()}

    # ---- mouth_says
    def mouth_says(self, top=1):
        """What the organ lets out this moment: its own entrance, nothing else.

        Read at the moment it is asked, because the organ works off the action
        the Life is letting out right now and off nothing that is kept anywhere.
        """
        got = self.express(top=top)
        return [f for f, _g in got]

    # ---- mouth_scores
    def mouth_scores(self):
        """How close the current action stands to each row -- the organ's own
        arithmetic, printed so a reading can be read rather than believed."""
        act = self.action()
        if _norm(act) <= 1e-12:
            return {}
        return {f: abs(_cos(act, row))
                for f, (row, _w) in self.expression_forms.items()}

    # ---- mouth_sent
    def mouth_sent(self):
        """Every moment's sending: a moment with nothing, one form, or several."""
        return list(self.sp_sent)

    # ---- mouth_swap
    def mouth_swap(self, one, other):
        """Exchange two forms' rows in the organ's own table, and nothing else.

        If what it says follows a row rather than a name, the answer turns over
        with this: that is the whole point of the reading.  A form it never met
        has no row to exchange, and that is reported as such rather than made up.
        """
        if one not in self.expression_forms or other not in self.expression_forms:
            return None
        fa, fb = self.expression_forms[one], self.expression_forms[other]
        self.expression_forms[one], self.expression_forms[other] = fb, fa
        oa, ob = self.expression_first[one], self.expression_first[other]
        self.expression_first[one], self.expression_first[other] = ob, oa
        return (one, other)

    # ---- mouth_table
    def mouth_table(self):
        """Everything the organ has really met: the row, the weight, the order."""
        return {"forms": {f: [list(row), float(w)]
                          for f, (row, w) in self.expression_forms.items()},
                "first": dict(self.expression_first),
                "met": int(self.expression_met)}

    # ---- msiu_lines
    def msiu_lines(self):
        v = self.msiu_view()
        out = []
        if not v["acted_on"]:
            out.append("no Connection is mismatched or broken, so MSIU has formed "
                       "nothing: no connection is mismatched or broken")
            return out
        for r in v["records"]:
            out.extend(self._ms_words(r))
            out.append("")
        if v["structures_msiu_caused_to_come_about"]:
            out.append("Structures MSIU caused to come about: %s"
                       % "  ".join("structure #%d" % i
                                   for i in
                                   v["structures_msiu_caused_to_come_about"]))
        else:
            out.append("MSIU caused no new Structure to come about: every "
                       "organisation it formed the base already had")
        out.append("this is what was formed, read as it is: the connections in "
                   "it are the ones that were already formed and still really "
                   "act, no element is named for anything, and no way of "
                   "repairing or of rebuilding is proposed here")
        return out

    # ---- msiu_view
    def msiu_view(self):
        """Everything MSIU holds, read out: which Connection, and what it formed."""
        out = []
        for i in range(len(self.ms_conn)):
            first = self.ms_first[i]
            out.append({
                "the_connection": self.ms_conn[i],
                "kind": self.ms_kind[i],
                "against_connection": self.ms_connection[i],
                "in_structure": self.ms_from_structure[i],
                "first_acted_at": self.ms_born[i],
                "formed_first": first,
                "that_was_new": bool(self.ms_first_new[i]),
                "formed_now": self.ms_structure[i] if self.ms_current[i] else -1,
                "still_current": bool(self.ms_current[i]),
                "moments_acted": self.ms_moments[i],
                "ends_that_were_still_there": list(self.ms_ends[i]),
                "connections_that_still_hold": [
                    {"connection": c, "between_end": x, "and_end": y,
                     "acts_now": round(self.cn_live[c], 6)}
                    for x, y, c in self.ms_pieces[i]],
                "ends_taking_part_in_nothing_that_runs": list(
                    self.ms_left_out[i]),
                "the_answers_it_gave": list(self.ms_trail[i]),
            })
        return {
            "records": out,
            "acted_on": len(self.ms_conn),
            "structures_msiu_caused_to_come_about": list(
                self.ms_new_structures),
            "moments_msiu_was_walked": self.msiu_moments,
            "moments_it_acted": self.msiu_acted,
        }

    # ---- msiu_state_lines
    def msiu_state_lines(self):
        """The same thing said out loud, without adding anything to it."""
        v = self.msiu_state_view()
        out = []
        if not v["come_about"]:
            out.append("nothing a connection is in has "
                       "asked for a change")
        for n in v["current"]:
            out.append("connection #%d  %s  between element #%d and "
                       "element #%d  in structure #%d  (came about at %d, "
                       "current %d moments in %d stretches)"
                       % (n["identity"], n["kind"], n["against_connection"],
                          n["between"][0], n["between"][1], n["in_structure"],
                          n["came_about"], n["moments_current"],
                          n["stretches_current"]))
        for n in v["not_current_any_more"]:
            out.append("connection #%d  %s  in structure #%d  is no "
                       "longer current (it stopped at %d; it was current %d "
                       "moments in %d stretches)"
                       % (n["identity"], n["kind"], n["against_connection"],
                          n["in_structure"], n["stopped"],
                          n["moments_current"], n["stretches_current"]))
        return out

    # ---- msiu_state_view   (this file's own: MSIU's own records, read out)
    def msiu_state_view(self):
        return {
            "current": self.msiu_now(),
            "not_current_any_more": [
                self._ms_desc(i) for i in range(len(self.ms_conn))
                if not self.ms_current[i]],
            "come_about": len(self.ms_conn),
            "moments_read": self.msiu_read_moments,
            "moments_with_no_state_yet": self.msiu_read_none,
        }

    # ---- msiu_now   (this file's own: what MSIU is rebuilding, now)
    def msiu_now(self):
        """What MSIU is rebuilding right now, read off MSIU's own records.

        There is no separate record of a "Need": the identity is the
        Connection's own, and what is being rebuilt now is exactly the set of
        Connections LAS showed as mismatched or broken on this moment.
        """
        return [self._ms_desc(i) for i in range(len(self.ms_conn))
                if self.ms_current[i]]

    # ---- ow_join
    def ow_join(self, owner, ends):
        """Declare that these ends are one participant's ports.

        Called once, for the Life, with the six behaviour ends.  An end is a
        port of exactly one participant, and a participant that owns nothing is
        its own: that is all "who" means here.
        """
        ends = [int(u) for u in ends]
        for u in ends:
            self.ow_owner[u] = owner
        got = self.ow_ports.setdefault(owner, [])
        for u in ends:
            if u not in got:
                got.append(u)
        return list(got)

    # ---- ow_lines
    def ow_lines(self):
        """The same, as lines, so a report can print it as it stands."""
        s = self.ow_snapshot()
        out = ["moment %d" % s["age"]]
        out.append("  the identity: %r, one of them, carrying %d port(s): %s"
                   % (s["identity"], s["port_count"], s["ports"]))
        out.append("  the participants that own ports, ever: %s" % (s["arrived"],))
        out.append("  elements holding the Life: %d ; structures holding it: %d"
                   % (len(s["elements_holding_the_life"]),
                      len(s["structures_holding_the_life"])))
        for e, ports in s["elements_holding_the_life"][:4]:
            out.append("    element %d holds the Life through %s" % (e, ports))
        for i, ports in s["structures_holding_the_life"][:4]:
            out.append("    structure #%d holds the Life through %s" % (i, ports))
        return out

    # ---- ow_snapshot
    def ow_snapshot(self):
        """Everything this ownership can answer, for one moment."""
        ports = self.ports_of(LIFE)
        return {
            "age": self.age,
            "identity": LIFE,
            "port_count": len(ports),
            "ports": [self.end_name(u) for u in ports],
            "port_values": {self.end_name(u): self.frame_now[u]
                            for u in ports if u < len(self.frame_now or [])},
            "arrived": sorted(set(self.ow_owner.values())),
            "elements_holding_the_life": [
                (e, [self.end_name(u) for u in self.el_participants(e)[1]])
                for e in range(len(self.el_ends))
                if LIFE in self.el_participants(e)[0]],
            "structures_holding_the_life": [
                (i, [self.end_name(u) for u in self.carries(i)])
                for i in range(len(self.st_ids)) if self.carries(i)],
        }

    # ---- ow_write
    def ow_write(self, path):
        """Keep the ownership tables beside the run, and nothing else."""
        rows = ["the Life's ports: %s"
                % [self.end_name(u) for u in self.ports_of(LIFE)]]
        rows.append("structures the Life really stood in, and through where:")
        for i in sorted(self.ow_st_moments):
            ports = [self.end_name(u) for u in self.ow_st_seen[i]["ports"]]
            rows.append("  structure #%d : first stood at moment %s ; the Life "
                        "in it on %d moment(s) ; ports ever seen in it: %s"
                        % (i, self.ow_st_first.get(i), self.ow_st_moments[i],
                           ports))
        io.open(path, "w", encoding="utf-8").write("\n".join(rows) + "\n")
        return path

    # ---- owners
    def owners(self):
        """Every participant that owns ports, and only those."""
        return sorted(self.ow_ports)

    # ---- participants
    def participants(self):
        """How many ends there are now: the reality, the behaviour, the Life,
        and every slot the one list holds."""
        if not getattr(self, "past_run_enabled", False):
            return self._base_units() + len(self.st_ids)
        return self._base_units() + len(self.unit_kind)

    # ---- _participants_step1
    def _participants_step1(self):
        """The channels, the Life, the formed Structures, and the runs.

        A run's slot is an end like any other; it is not a copy and not a
        Structure, and it is not made of anything.
        """
        if not getattr(self, "past_run_enabled", False):
            return self._base_units() + len(self.st_ids)
        return self._base_units() + len(self.unit_kind)

    # ---- _participants_step2
    def _participants_step2(self):
        """How many ends there are now: the reality, the Life, the Structures."""
        return self._base_units() + len(self.st_ids)

    # ---- _participants_step3
    def _participants_step3(self):
        """How many ends there are now: the channels, then every Structure."""
        return self._channels() + len(self.st_ids)

    # ---- past_run_check
    def past_run_check(self):
        """The slots and the bringings read for mistakes, none repaired.

        Five things must hold and none of them can be made to hold by a choice
        this implementation makes: a run that can be brought back has a slot of its
        own; no slot stands for two things and no two things share a slot; a
        slot stands for a run or a Structure and never both; every connection a
        run was brought back by really points at that run through its own formed
        way; and a run that is not brought back carries nothing.

        What is not checked here is the acting itself, because it is the moment
        before's and cannot be read again afterwards; that is checked from
        outside, in the round's own reading, where the acting of each moment is
        kept before the walk.
        """
        bad = []
        if not self.past_run_enabled:
            return bad
        seen = {}
        for e, slot in enumerate(self.rn_unit):
            if slot < 0:
                if e in set(self.sf_run.values()):
                    bad.append((e, slot, "a run a formed way points at but no "
                                "slot"))
                continue
            if slot in seen:
                bad.append((e, slot, "the same slot as run %d" % seen[slot]))
            seen[slot] = e
            if self.run_of_unit(slot) != e:
                bad.append((e, slot, "the slot does not read back as this run"))
            if self.structure_of_unit(slot) >= 0:
                bad.append((e, slot, "the slot reads as a Structure as well"))
            if not (self._base_units() <= slot < self.participants()):
                bad.append((e, slot, "the slot is outside the one list"))
        for i, slot in enumerate(self.st_unit):
            if slot < 0:
                continue
            if self.structure_of_unit(slot) != i:
                bad.append((i, slot, "the slot does not read back as this "
                            "Structure"))
        for e in range(len(self.rn_unit)):
            for k in (self.rn_by[e] if e < len(self.rn_by) else []):
                if self.sf_run.get(k, -1) != e:
                    bad.append((e, k, "said to be brought back by a connection "
                                "that does not point at it"))
                if k >= len(self.cn_pre):
                    bad.append((e, k, "no such connection"))
            if not self.rn_on[e] and self.rn_form[e] != 0.0:
                bad.append((e, self.rn_unit[e], "not brought back but carrying "
                            "something"))
        for k, e in self.sf_run.items():
            if not (0 <= e < len(self.rn_start)):
                bad.append((k, e, "a way pointing at no run"))
        return bad

    # ---- past_run_lines
    def past_run_lines(self):
        v = self.past_run_view()
        out = []
        if not v["enabled"]:
            out.append("no past run takes part: the ability is off")
            return out
        out.append("the kept runs and the slots they were given, read over %d "
                   "moments:" % v["moments_read"])
        out.append("   runs %d, given a slot of their own: %d, left without "
                   "one: %d   (ends %d: %d before the runs, %d of them)"
                   % (v["runs"], v["slots_given"], v["runs_without_a_slot"],
                      v["ends_now"],
                      v["ends_from_reality_and_life_and_structures"],
                      v["ends_from_runs"]))
        out.append("   runs brought back at least once: %d; brought back now: "
                   "%d; moments with something brought back: %d"
                   % (v["runs_brought_back_ever"], v["runs_brought_back_now"],
                      v["moments_something_was_brought_back"]))
        for d in v["run_list"]:
            if not d["given_a_slot"]:
                continue
            if not d["moments_brought_back"]:
                out.append("   run %-4d s%-4d #%-3d from %-7d to %-12s  slot "
                           "%-4d  never brought back"
                           % (d["run"], d["structure"], d["ordinal"],
                              d["start"],
                              "still going" if d["still_running"]
                              else str(d["stop"]), d["slot"]))
                continue
            out.append("   run %-4d s%-4d #%-3d from %-7d to %-12s  slot %-4d  "
                       "%d moment(s) in %d stretch(es), by %s"
                       % (d["run"], d["structure"], d["ordinal"], d["start"],
                          "still going" if d["still_running"]
                          else str(d["stop"]), d["slot"],
                          d["moments_brought_back"],
                          len(d["stretches_brought_back"]),
                          " ".join("#%d" % k for k
                                   in d["connections_that_point_at_it"])
                          or "nothing"))
            for x, y in d["stretches_brought_back"]:
                out.append("        brought back from %-7d to %-12s"
                           % (x, ".." if y is None else str(y)))
        return out

    # ---- past_run_participation
    def past_run_participation(self):
        """What the runs that are slots are really ends of now.

        Read off the base's own tables: a connection is one that has a run's
        slot as one of its two ends, an element is one that has a run's slot
        among what it is made of, and a Structure is one whose elements reach a
        run's slot.  Nothing is counted that is not in those tables.
        """
        slots = set(u for u in self.rn_unit if u >= 0)
        by_slot = {u: self.run_of_unit(u) for u in slots}
        conns = []
        for k in range(len(self.cn_pre)):
            a, b = self.cn_pre[k], self.cn_post[k]
            if a in slots or b in slots:
                conns.append({
                    "connection": k, "pre": a, "post": b,
                    "acts_now": round(self.cn_live[k], 9),
                    "really_acting": self.cn_live[k] >= self._own_conn_bar(),
                    "born": self.cn_born[k],
                    "the_run_slot": a if a in slots else b,
                    "the_run": by_slot[a if a in slots else b],
                })
        ends = []
        for i in range(len(self.el_ends)):
            hit = sorted(by_slot[u] for u in self.el_ends[i] if u in slots)
            if hit:
                ends.append({"end": i, "members": list(self.el_ends[i]),
                             "runs_in_it": hit,
                             "born": self.el_born[i],
                             "frames": self.el_frames[i]})
        structs = []
        for i in range(len(self.st_ids)):
            got = self._runs_in_structure(i)
            if got:
                structs.append({"structure": i, "born": self.st_born[i],
                                "frames": self.st_frames[i],
                                "runs_in_it": got})
        return {
            "runs_that_are_slots": len(slots),
            "connections_with_a_run_at_one_end": conns,
            "elements_with_a_run_in_them": ends,
            "structures_with_a_run_in_them": structs,
        }

    # ---- past_run_view
    def past_run_view(self):
        """Every kept run, its slot, and the moments it was brought back."""
        rows = [self._pr_of(e) for e in range(len(self.rn_start))]
        return {
            "enabled": self.past_run_enabled,
            "every_run_given_one": self.past_run_all,
            "moments_read": self.pr_moments,
            "moments_skipped": self.pr_skipped,
            "runs": len(self.rn_start),
            "slots_given": self.pr_slots_given,
            "runs_without_a_slot": sum(1 for d in rows if not d["given_a_slot"]),
            "runs_brought_back_ever": sum(1 for n in self.rn_brought if n),
            "runs_brought_back_now": sum(1 for b in self.rn_on if b),
            "moments_something_was_brought_back": self.pr_bringing,
            "first_brought_back_at": self.pr_first_back,
            "ends_now": self.participants(),
            "ends_from_reality_and_life_and_structures":
                self._base_units() + len(self.st_ids),
            "ends_from_runs": sum(1 for k in self.unit_kind if k == "r"),
            "run_list": rows,
        }

    # ---- port_index
    def port_index(self, unit):
        """Which of its owner's ports this end is, counting from nothing."""
        o = self.ow_owner.get(unit)
        if o is None:
            return -1
        return self.ow_ports[o].index(unit)

    # ---- ports_of
    def ports_of(self, owner):
        """Every end a participant carries its own doings out on."""
        return list(self.ow_ports.get(owner, []))

    # ---- reset_activity_state
    def reset_activity_state(self):
        n = self.dna.state_size
        self.state = [0.0] * n
        self.change_baseline = 0.0
        self.last_delta = 0.0
        self.last_drive = [0.0] * n
        self.age = 0
        return self

    # ---- run_history_check
    def run_history_check(self):
        """The runs against the base's own counting, read for mistakes.

        Three things must hold, and cannot be made to hold by any choice this
        implementation makes: a Structure's runs must add up to exactly the moments the
        base counted it as running; within one Structure the runs must come in
        order and must not overlap; and a Structure must not have two runs going
        at once.  Anything else is reported, not repaired.
        """
        bad = []
        if not self.run_history_enabled:
            return bad
        for i in range(len(self.st_frames)):
            r = self._rn_of(i)
            total, prev_stop, going = 0, -1, 0
            for d in r["run_list"]:
                total += d["moments"]
                going += 1 if d["still_running"] else 0
                if d["start"] <= prev_stop:
                    bad.append((i, d["run"], "begins before the run before "
                                "it stopped"))
                prev_stop = (10 ** 18 if d["still_running"]
                             else d["start"] + d["moments"])
            if total != self.st_frames[i]:
                bad.append((i, -1, "run moments %d against the base's own %d"
                            % (total, self.st_frames[i])))
            if going > 1:
                bad.append((i, -1, "%d runs still going at once" % going))
            if len(r["run_list"]) != (self.st_run_ord[i]
                                      if i < len(self.st_run_ord) else 0):
                bad.append((i, -1, "runs listed do not match the ordinal"))
        for e in range(len(self.rn_start)):
            if self.rn_stop[e] is not None and self.rn_stop[e] <= self.rn_start[e]:
                bad.append((self.rn_struct[e], e, "stops before it begins"))
        return bad

    # ---- run_history_lines
    def run_history_lines(self, structure=None):
        """The runs, written out the way the base writes its own reading."""
        v = self.run_history_view(structure)
        out = []
        if not v["enabled"]:
            out.append("no Structure keeps its runs: the ability is off")
            return out
        out.append("the runs of every Structure, %d read over %d moments:"
                   % (v["structures"], v["moments_read"]))
        out.append("   Structures %d, of which %d have run at least once and "
                   "%d have never run; runs %d, of which %d are still going"
                   % (v["structures"], v["structures_with_runs"],
                      v["structures_never_run"], v["runs"],
                      v["runs_still_going"]))
        for r in v["structures_list"]:
            if not r["runs"] and structure is None:
                continue
            out.append("   s%-4d born %-7d ran %-6d moments in %d run(s)"
                       % (r["structure"], r["born"],
                          r["moments_run_altogether"], r["runs"]))
            for d in r["run_list"]:
                stop = "still going" if d["still_running"] else str(d["stop"])
                out.append("        run %-4d #%-3d  from %-7d to %-12s  %d "
                           "moment(s)"
                           % (d["run"], d["ordinal"], d["start"], stop,
                              d["moments"]))
        return out

    # ---- run_history_view
    def run_history_view(self, structure=None):
        """Every run every Structure has had, read out as it is kept."""
        if not self.run_history_enabled:
            return {"enabled": False, "moments_read": 0, "moments_skipped":
                    self.rn_skipped}
        n = len(self.st_frames)
        which = range(n) if structure is None else \
            [structure] if 0 <= structure < n else []
        rows = [self._rn_of(i) for i in which]
        got = [r for r in rows if r["runs"]]
        return {
            "enabled": True,
            "moments_read": self.rn_moments,
            "moments_skipped": self.rn_skipped,
            "structures": n,
            "structures_with_runs": len(got),
            "structures_never_run": n - len(got),
            "structures_running_now": sum(1 for r in rows if r["running_now"]),
            "runs": len(self.rn_start),
            "runs_still_going": sum(1 for t in self.rn_stop if t is None),
            "structures_list": rows,
        }

    # ---- run_of_unit
    def run_of_unit(self, unit):
        """Which run a slot stands for, or -1 when it stands for something
        else.  A run's slot is the only thing here that is a run.
        """
        if not getattr(self, "past_run_enabled", False):
            return -1
        k = unit - self._base_units()
        if 0 <= k < len(self.unit_kind) and self.unit_kind[k] == "r":
            return self.unit_ref[k]
        return -1

    # ---- run_sf_view
    def run_sf_view(self):
        """Every run, and the ways first written in it -- the other direction."""
        by = {}
        for k, e in self.sf_run.items():
            by.setdefault(e, []).append(k)
        out = []
        for e in range(len(self.rn_start)):
            ks = sorted(by.get(e, []))
            out.append({"run": e, "structure": self.rn_struct[e],
                        "ordinal": self.rn_ord[e],
                        "start": self.rn_start[e], "stop": self.rn_stop[e],
                        "still_running": self.rn_stop[e] is None,
                        "ways_formed_here": ks, "ways": len(ks)})
        return out

    # ---- running_mode
    def running_mode(self):
        amp = self.dna.mode_amp
        return [1.0 + amp * math.tanh(v) for v in self.tissue]

    # ---- runtime_slots
    def runtime_slots(self):
        slots = []
        for name, value in sorted(vars(self).items()):
            if isinstance(value, list):
                slots.append((name, len(value)))
            elif isinstance(value, (int, float)):
                slots.append((name, 1))
        return slots

    # ---- say_now
    def say_now(self):
        """One moment's answer, with the arithmetic that produced it."""
        act = [float(x) for x in self.action()]
        cands = self.express(top=0) if self.expression_enabled else []
        best = cands[0][1] if cands else None
        second = cands[1][1] if len(cands) > 1 else None
        rows = {f: list(e[0]) for f, e in self.expression_forms.items()}
        met = {f: self.expression_first[f] for f in self.expression_forms}
        return {
            "age": self.age, "act": act, "norm": _norm(act),
            "said": cands[0][0] if cands else None,
            "band": [f for f, _s in cands], "n_band": len(cands),
            "best": best, "second": second,
            "gap": (best - second) if (best is not None and second is not None)
            else None,
            "n_forms": len(self.expression_forms),
            "rows": rows, "met": met,
            "scores": {f: _cos(act, r) for f, r in rows.items()},
            "first_met_order": sorted(met, key=lambda f: met[f]),
            "forms": {n: self.form_now(n) for n in WORDS},
            "st_n": len(self.st_ids), "cur_el": list(self.cur_el),
            "cur_st": list(self.cur_st), "cells": list(self.frame_now or []),
            "state": list(self.state), "action": act,
        }

    # ---- self_perception_lines
    def self_perception_lines(self):
        v = self.self_perception_view()
        out = []
        if not v["enabled"]:
            out.append("this Life has no self-perceiving unit: the ability is off")
            return out
        out.append("the Life unit is unit %d, the same identity since the "
                   "instance began" % v["the_unit"])
        out.append("   it carries now %+.9f  (the whole-reading, taken the "
                   "moment before)" % v["carries_now"])
        out.append("   connections it is in that still act now: %d"
                   % len(v["connections_it_is_in_that_act"]))
        for d in v["connections_it_is_in_that_act"]:
            out.append("     #%-4d %-24s  acts %.6f"
                       % (d["connection"], d["direction"], d["acts_now"]))
        out.append("   ends it is in: %d   Structures it is in: %d"
                   % (len(v["ends_it_is_in"]), len(v["structures_it_is_in"])))
        for d in v["structures_it_is_in"]:
            out.append("     structure #%d  born %s  ran %d moments"
                       % (d["structure"], d["born"], d["frames"]))
        return out

    # ---- self_perception_view
    def self_perception_view(self):
        """The Life unit, read as it is: where it is, and what it is in now."""
        u = self._self_unit()
        if u < 0:
            return {"enabled": False, "the_unit": -1}
        live = []
        bar = self._own_conn_bar()
        for k in range(len(self.cn_pre)):
            if self.cn_pre[k] == u or self.cn_post[k] == u:
                if self.cn_live[k] < bar:
                    continue
                other = self.cn_post[k] if self.cn_pre[k] == u else self.cn_pre[k]
                live.append({
                    "connection": k,
                    "acts_now": round(self.cn_live[k], 9),
                    "the_other_end_is_a_structure": other >= self._base_units(),
                    "the_other_end": other,
                    "direction": ("the Life acts on it"
                                  if self.cn_pre[k] == u
                                  else "it acts on the Life"),
                })
        ends = [e for e in range(len(self.el_ends)) if u in self.el_ends[e]]
        sts = []
        for i in range(len(self.st_ids)):
            on = set()
            for e in self.st_ends[i]:
                on.update(self.element_reach(e))
            if u in on:
                sts.append({"structure": i, "born": self.st_born[i],
                            "frames": self.st_frames[i]})
        return {
            "enabled": True,
            "the_unit": u,
            "carries_now": round(self.lf_form, 9),
            "connections_it_is_in_that_act": live,
            "ends_it_is_in": ends,
            "structures_it_is_in": sts,
            "moments_carried": self.lf_moments,
            "moments_skipped": self.lf_skipped,
        }

    # ---- set_behavior
    def set_behavior(self, done):
        """What the behaviour organ actually executed, handed to these ends.

        This is not a way in for reality: nothing here is built from a frame and
        nothing here reaches the Life's perception.  It sets the values of the
        ends that stand for what this Life itself did, exactly as a channel
        carries the value of the reality it was handed.
        """
        done = [float(x) for x in done]
        if len(done) != self.behavior_count:
            raise ValueError("the organ hands over %d value(s), expected %d"
                             % (len(done), self.behavior_count))
        for v in done:
            if v != v or abs(v) == float("inf"):
                raise ValueError("what the Life did must be finite")
        self.bh_now = done
        self.bh_set_moments += 1
        return list(self.bh_now)

    # ---- sf_cost
    def sf_cost(self):
        """What the three-state history physically holds: entries, and stretches."""
        return sf_cost(self)

    # ---- sf_pos
    def sf_pos(self, k):
        """How many moments this connection has been judged, up to now."""
        at = self.walk_sf_at.get(k)
        if at is None:
            return 0
        return self.sf_moments - at

    # ---- sf_run_check
    def sf_run_check(self):
        """The pairing read for mistakes, none of them repaired.

        Four things must hold, and none can be made to hold by any choice this
        implementation makes: a connection given a run must have a formed way; the run
        must be one that exists; it must belong to the very Structure the way
        says it was formed in; and no connection may be given more than one --
        a way is written once, so it is pointed at a run once.

        Several connections pointing at one run is not a mistake: one running
        of an organisation can lay down the basis of several connections at
        once, and it is expected.  What may not happen is one connection
        pointing at two runs, or at a run of some other Structure.
        """
        bad = []
        if not self.sf_run_enabled:
            return bad
        for k, e in sorted(self.sf_run.items()):
            if k not in self.sf_way:
                bad.append((k, e, "given a run but has no formed way"))
                continue
            if not (0 <= e < len(self.rn_start)):
                bad.append((k, e, "no such run"))
                continue
            if self.rn_struct[e] != self.sf_born_in.get(k, -1):
                bad.append((k, e, "the run belongs to another Structure than "
                            "the one the way was formed in"))
        if self.run_history_enabled and len(self.sf_run) != len(self.sf_way):
            bad.append((-1, -1, "%d formed ways but only %d are given a run, "
                        "though the runs are being kept"
                        % (len(self.sf_way), len(self.sf_run))))
        if len(self.sf_run) != self.sf_run_written:
            bad.append((-1, -1, "%d connections are given a run but %d were "
                        "counted as given one" % (len(self.sf_run),
                                                  self.sf_run_written)))
        return bad

    # ---- sf_run_lines
    def sf_run_lines(self):
        """The pairing, written out the way the base writes its own reading."""
        v = self.sf_run_view()
        out = []
        if not v["enabled"]:
            out.append("no way remembers its run: the ability is off")
            return out
        out.append("the ways and the runs they came out of, read over %d "
                   "moments:" % v["moments_read"])
        out.append("   formed ways %d, of which %d are given a run and %d are "
                   "left without one"
                   % (v["ways_there_are"], v["ways_given_a_run"],
                      v["ways_left_without_one"]))
        out.append("   runs that laid down more than one connection at once: %d"
                   % v["runs_with_more_than_one"])
        for d in v["connections"]:
            if d["from_a_run"]:
                out.append("   #%-4d %-8s -> %-8s  formed in s%-4d  run %-4d "
                           "#%-3d  from %-7d to %-12s  way %+d"
                           % (d["connection"], "u%d" % d["pre"],
                              "u%d" % d["post"], d["formed_in"],
                              d["origin_run"], d["origin_ordinal"],
                              d["origin_start"],
                              "still going" if d["origin_stop"] is None
                              else str(d["origin_stop"]), d["way"]))
            else:
                out.append("   #%-4d %-8s -> %-8s  formed in s%-4d  no run"
                           % (d["connection"], "u%d" % d["pre"],
                              "u%d" % d["post"], d["formed_in"]))
        return out

    # ---- sf_run_shared
    def sf_run_shared(self):
        """Runs that laid down more than one connection's basis at once.

        Not a mistake and not a check: one running of an organisation may give
        several of its connections their way in the same moment, and this is
        how many did.
        """
        n = {}
        for e in self.sf_run.values():
            n[e] = n.get(e, 0) + 1
        return {e: c for e, c in n.items() if c > 1}

    # ---- sf_run_view
    def sf_run_view(self):
        """Every connection with a formed way, and the run it came out of."""
        rows = []
        for k in sorted(self.sf_way):
            e = self.sf_run.get(k, -1)
            d = {"connection": k, "pre": self.cn_pre[k], "post": self.cn_post[k],
                 "born": self.cn_born[k], "way": self.sf_way[k],
                 "formed_in": self.sf_born_in.get(k, -1),
                 "origin_run": e, "from_a_run": e >= 0}
            if e >= 0:
                d["origin_ordinal"] = self.rn_ord[e]
                d["origin_start"] = self.rn_start[e]
                d["origin_stop"] = self.rn_stop[e]
                d["origin_moments"] = self._rn_moments_of(e)
                d["origin_begins_there"] = self.rn_start[e]
            rows.append(d)
        return {
            "enabled": self.sf_run_enabled,
            "moments_read": self.sf_run_moments,
            "moments_skipped": self.sf_run_skipped,
            "ways_there_are": len(self.sf_way),
            "ways_given_a_run": len(self.sf_run),
            "ways_left_without_one": len(self.sf_way) - len(self.sf_run),
            "moments_a_way_had_no_run": self.sf_run_openless,
            "ways_given_a_run_already_going": self.sf_run_midrun,
            "runs_with_more_than_one": len(self.sf_run_shared()),
            "connections": rows,
        }

    # ---- sf_seed
    def sf_seed(self, k):
        """Give one connection the state it stands in, counted for one moment.

        This is for history handed to a Life that has not lived it -- a
        connection that once existed and no longer takes part: it is in `stable`
        now, it has been for the one moment it is counted for, and its own
        series begins there.  Nothing that is going on is touched.
        """
        self.sf_wrap()
        runs = self._sf_runs_for(k)
        runs["state"].put(STABLE, 1)
        runs["live"].put(0.0, 1)
        runs["form"].put(0.0, 1)
        self.walk_sf_open[k] = (STABLE, 1)
        self.walk_sf_at[k] = self.sf_moments - 1

    # ---- sf_walked
    def sf_walked(self):
        """The connections judged on the last moment, and the ones left out.

        The second number is the whole point of the round: a connection whose
        own reading did not move was not judged, and its stretch simply lasts.
        """
        return {"there": self.walk_sf_there, "judged": self.walk_sf_walked,
                "left out": self.walk_sf_skipped}

    # ---- sf_wrap
    def sf_wrap(self, ahead=0):
        """Take a plain history in, and leave every answer it gave as it was.

        A Life that lived with the switch off -- or one read back, or one the
        guard's own inflation handed rows to -- holds `sf_hist` and its two
        companions as plain lists of one entry per judged moment, and
        `sf_frames` as the counts the base wrote for them.  Taking them in
        changes no value, no length and no order: the same moments are read off
        the stretches that produced them, the same counts are added up from
        those stretches, and nothing is written down again that was not asked
        for.  It is what lets the switch be turned on part way through a life,
        not only before it.

        `ahead` is what the Life has already counted but not yet written down.
        The base's own `_sf_step` counts a moment (:131) before it judges
        it (:132), so when this is called from inside the judge the moment
        at hand is one further on than the history has reached.

        Called with nothing to take in -- the ordinary case, a Life built with
        the switch on -- it does nothing at all.
        """
        if not getattr(self, "sf_runs_enabled", False):
            return
        if self.walk_sf_wrapped:
            return
        self.walk_sf_wrapped = True
        if not isinstance(self.sf_frames, Frames):
            self.sf_frames = Frames(self, self.sf_frames)
        for k, hist in list(self.sf_hist.items()):
            if isinstance(hist, Series):
                continue          # taken in already: its counts stand as they are
            # read the two companions before the series replace them: taking
            # the three in puts a fresh series in each of their places
            live = self.sf_live_hist.get(k, ())
            form = self.sf_form_hist.get(k, ())
            runs = self._sf_runs_for(k)
            runs["state"].seed(hist)
            runs["live"].seed(live)
            runs["form"].seed(form)
            if self.walk_sf_at.get(k) is None:
                # the moment it was first judged, read off its own history
                self.walk_sf_at[k] = self.sf_moments - ahead - len(hist)
            self._sf_recount(k, runs["state"])

    # ---- show
    def show(self, forms):
        """What the outside really shows this moment, and nothing else.

        Called before the moment runs, so a form is a participant of the moment
        it arrived in.  A form that has never really appeared is noted here and
        given its place as this moment's walk begins; one that has appeared
        before keeps the identity and the place it already has.
        """
        want = {}
        for name in forms:
            if name not in self.wd_unit and name not in self.wd_pending:
                self.wd_pending.append(name)
                self.wd_seen[name] = 0
                self.wd_born[name] = self.age
            want[name] = 1.0
            self.wd_seen[name] += 1
        self.wd_now = want
        self.wd_shown = list(forms)
        self.wd_moments += 1
        return want

    # ---- snapshot
    def snapshot(self):
        return list(self.state)

    # ---- source_drive
    def source_drive(self, v):
        return self._base_dna.source_drive(v)

    # ---- source_sample
    def source_sample(self, src):
        if src == 1:
            return [1.0, 0.0]
        if src == 2:
            return [0.0, 1.0]
        if src == 0:
            return [0.0, 0.0]
        raise ValueError("source channel must be 1 or 2 (0 = control condition)")

    # ---- st_participants
    def st_participants(self, i):
        """Which participants a structure is made of, and through which ports."""
        owners, ports = [], []
        for e in self.st_ends[i]:
            one, one_ports = self.el_participants(e)
            for o in one:
                if o not in owners:
                    owners.append(o)
            for u in one_ports:
                if u not in ports:
                    ports.append(u)
        return owners, sorted(ports)

    # ---- state_norm
    def state_norm(self) -> float:
        return math.sqrt(sum(v * v for v in self.state))

    # ---- state_now
    def state_now(self):
        """What this moment's running came to: who took part, and the one list."""
        self._align_now()
        cur_el, cur_st = set(self.cur_el), set(self.cur_st)
        slots = {i: (self.st_unit[i] if i < len(self.st_unit) else -1)
                 for i in range(len(self.st_ids))}
        part_slots = [s for i, s in slots.items() if i in cur_st and s >= 0]
        idle_slots = [s for i, s in slots.items() if i not in cur_st and s >= 0]
        vals = list(self.frame_now or [])
        idle_nonzero = [i for i, s in slots.items()
                        if i not in cur_st and 0 <= s < len(vals) and vals[s] != 0.0]
        part_zero = [i for i, s in slots.items()
                     if i in cur_st and 0 <= s < len(vals) and vals[s] == 0.0]
        return {
            "age": self.age,
            "state": list(self.state),
            "action": list(self.action()),
            "cells": vals,
            "cur_el": sorted(cur_el), "cur_st": sorted(cur_st),
            "part_slots": part_slots, "idle_slots": idle_slots,
            "idle_cells": [vals[s] for s in idle_slots if s < len(vals)],
            "idle_nonzero_ids": idle_nonzero, "part_zero_ids": part_zero,
            "part_cells_nonzero": sum(1 for s in part_slots
                                      if s < len(vals) and vals[s] != 0.0),
            "el_n": len(self.el_ends), "st_n": len(self.st_ids),
            "el_seen": sum(1 for v in self.el_frames if v > 0),
            "st_seen": sum(1 for v in self.st_frames if v > 0),
            "el_idle": sum(1 for i, v in enumerate(self.el_frames)
                           if v > 0 and i not in cur_el),
            "st_idle": sum(1 for i, v in enumerate(self.st_frames)
                           if v > 0 and i not in cur_st),
        }

    # ---- state_size
    def state_size(self) -> int:
        return len(self.state)

    # ---- state_summary
    def state_summary(self):
        """One line per connection that has ever been judged."""
        out = []
        for k in sorted(self.sf_state):
            fr = [self.sf_frames.get((k, s), 0) for s in (STABLE, MISMATCH, BROKEN)]
            out.append({
                "connection": k,
                "pre": self.cn_pre[k], "post": self.cn_post[k],
                "born": self.cn_born[k],
                "now": STATE_NAMES[self.sf_state[k]],
                "moments": sum(fr), "stable": fr[0], "mismatch": fr[1],
                "broken": fr[2],
                "live": round(self.cn_live[k], 6),
                "peak": round(self.cn_peak[k], 6),
                "form": round(self.cn_form[k], 6)
                if self.cn_form[k] is not None else None,
                "formed_way": self.sf_way.get(k),
                "formed_in_structure": self.sf_born_in.get(k),
            })
        return out

    # ---- states_now
    def states_now(self):
        return {k: STATE_NAMES[self.sf_state[k]] for k in sorted(self.sf_state)}

    # ---- step
    def step(self, frame, src=1, form=None):
        out = self._step_step1(frame, src, form=form)
        if self.sp_keep:
            self.sp_say.append(self.say_now())
        return out

    # ---- _step_step1
    def _step_step1(self, frame, src=1, form=None):
        self.sp_now = []
        return self._step_step2(frame, src, form=form)

    # ---- _step_step2
    def _step_step2(self, frame, src=1, form=None):
        """One moment: the form present in the list first, then the organ."""
        self.show([form] if form is not None else [])
        return self._step_step3(frame, src, form=form)

    # ---- _step_step3
    def _step_step3(self, frame, src=1, form=None):
        """One moment of the Life, and the form that arrived with it.

        `super().step` is the trunk's, which calls `_meet(frame)` itself.  With a
        frame of six numbers that call returns at once (only a single character
        counts as a form), so the trunk's own perception is exactly as before and
        the form lane below is the only way a form gets in.
        """
        return self._step_step4(frame, src)

    # ---- _step_step4
    def _step_step4(self, frame, src=1):
        """One moment, and -- if it is asked for -- the reading of it.

        The signature is the trunk's own: a form is not this implementation's business
        and is never taken here, exactly as in the base.
        """
        out = self._step_step5(frame, src)
        if self.keep_log:
            self.join_log.append(self.state_now())
        return out

    # ---- _step_step5
    def _step_step5(self, frame, src=1):
        return self._step_step6(frame, src)

    # ---- _step_step6
    def _step_step6(self, frame, src=1):
        """Hand the trunk exactly what it was handed, and the base the carrier.

        The frame itself is passed on untouched: the trunk's own entry is what
        turns it into the carrier, and one of its layers keeps the frame as the
        symbol this moment is filed under, so it must arrive as it always did.
        """
        carrier = list(self.inlet.frame(frame))
        self.cog_frame = carrier
        self.frame_now = carrier
        try:
            return self._step_step8(frame, src)
        finally:
            self.cog_frame = None

    # ---- _step_step7
    def _step_step7(self, frame, src=1):
        self.frame_now = [float(x) for x in frame]
        return self._step_step8(frame, src)

    # ---- _step_step8
    def _step_step8(self, ch, src=1):
        self._mem_have_input = True
        try:
            return self._step_step10(ch, src)
        finally:
            self._mem_have_input = False

    # ---- _step_step10
    def _step_step10(self, ch, src=1):
        self._frame_source = self.source_sample(src)
        return self._step_step11(ch)

    # ---- _step_step11
    def _step_step11(self, frame):
        r = self.inlet.frame(frame)
        dna = self.dna
        s = self.state
        n = len(s)
        d = dna.channel_count
        m = dna.latent_count

        real_drive = dna.entry_drive(r)
        internal = dna.internal_coupling(s)
        mode = self.running_mode()
        kappa, eta, gamma = dna.kappa, dna.eta, dna.gamma
        rho = dna.latent_rate
        A = self.coupling

        a_new = [0.0] * m
        for j in range(m):
            u = dna.latent_entry[j]
            acc = 0.0
            for k in range(d):
                acc += u[k] * r[k]
            a_new[j] = (1.0 - rho) * self.latent_activity[j] + rho * math.tanh(acc)

        feedback = [0.0] * n
        for j in range(m):
            aj = a_new[j]
            if aj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                feedback[i] += row[i] * aj
        inv_m = 1.0 / m
        inj = dna.injection

        # provisional (the third step)
        s_reality = [0.0] * n
        for i in range(n):
            drive_reality = real_drive[i] + kappa * internal[i] + inj * feedback[i] * inv_m
            s_reality[i] = s[i] + eta * (math.tanh(drive_reality) - gamma * mode[i] * s[i])
        self.last_state_reality = s_reality

        d_reality = [s_reality[i] - s[i] for i in range(n)]
        self.last_d_reality = d_reality

        ef = self.experience_flow
        self.experience_flow = [(1.0 - rho) * ef[i] + rho * d_reality[i] for i in range(n)]

        cue = self.experience_flow
        self.last_cue = self._shape(cue) or [0.0] * n
        if self.trace_enabled and self.trace_injection_on and dna.trace_gain > 0.0:
            trace_in, w, g = self.touch_traces(cue)
            mu = dna.trace_gain
        else:
            if self.trace_enabled:
                trace_in, w, g = self.touch_traces(cue)
            else:
                trace_in, w, g = [0.0] * n, [], []
                self.last_trace_g, self.last_trace_w = [], []
                self.last_trace_in, self.last_trace_fired = [0.0] * n, 0
            mu = 0.0

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = (real_drive[i] + kappa * internal[i] + inj * feedback[i] * inv_m
                     + mu * trace_in[i])
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
        self.latent_activity = a_new

        self._write_tissue(drive_out)
        if self.growth_enabled:
            self._grow(a_new, s)

        if self.trace_enabled:
            self.update_traces_split(cue, new_state, w, g)

        return {"tick": self.age, "delta": delta, "baseline": self.change_baseline,
                "same_or_different": delta - self.change_baseline,
                "trace_fired": self.last_trace_fired}

    # ---- _step_step12
    def _step_step12(self, frame):
        r = self.inlet.frame(frame)
        dna = self.dna
        s = self.state
        n = len(s)
        d = dna.channel_count
        m = dna.latent_count

        real_drive = dna.entry_drive(r)
        internal = dna.internal_coupling(s)
        mode = self.running_mode()
        kappa, eta, gamma = dna.kappa, dna.eta, dna.gamma
        rho = dna.latent_rate
        A = self.coupling

        a_new = [0.0] * m
        for j in range(m):
            u = dna.latent_entry[j]
            acc = 0.0
            for k in range(d):
                acc += u[k] * r[k]
            a_new[j] = (1.0 - rho) * self.latent_activity[j] + rho * math.tanh(acc)

        feedback = [0.0] * n
        for j in range(m):
            aj = a_new[j]
            if aj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                feedback[i] += row[i] * aj
        inv_m = 1.0 / m
        inj = dna.injection

        if self.trace_enabled and self.trace_injection_on and dna.trace_gain > 0.0:
            trace_in, w, g = self.touch_traces(s)
            mu = dna.trace_gain
        else:
            if self.trace_enabled:
                trace_in, w, g = self.touch_traces(s)
            else:
                trace_in, w, g = [0.0] * n, [], []
                self.last_trace_g, self.last_trace_w = [], []
                self.last_trace_in, self.last_trace_fired = [0.0] * n, 0
            mu = 0.0

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = (real_drive[i] + kappa * internal[i] + inj * feedback[i] * inv_m
                     + mu * trace_in[i])
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
        self.latent_activity = a_new

        self._write_tissue(drive_out)
        if self.growth_enabled:
            self._grow(a_new, s)

        if self.trace_enabled:
            self.update_traces(s, w, g)

        return {"tick": self.age, "delta": delta, "baseline": self.change_baseline,
                "same_or_different": delta - self.change_baseline,
                "trace_fired": self.last_trace_fired}

    # ---- _step_step13
    def _step_step13(self, frame):
        r = self.inlet.frame(frame)
        dna = self.dna
        s = self.state
        n = len(s)
        d = dna.channel_count
        m = dna.latent_count

        real_drive = dna.entry_drive(r)
        internal = dna.internal_coupling(s)
        mode = self.running_mode()
        kappa, eta, gamma = dna.kappa, dna.eta, dna.gamma
        rho = dna.latent_rate
        A = self.coupling

        a_new = [0.0] * m
        for j in range(m):
            u = dna.latent_entry[j]
            acc = 0.0
            for k in range(d):
                acc += u[k] * r[k]
            a_new[j] = (1.0 - rho) * self.latent_activity[j] + rho * math.tanh(acc)

        feedback = [0.0] * n
        for j in range(m):
            aj = a_new[j]
            if aj == 0.0:
                continue
            row = A[j]
            for i in range(n):
                feedback[i] += row[i] * aj
        inv_m = 1.0 / m
        inj = dna.injection

        new_state = [0.0] * n
        drive_out = [0.0] * n
        for i in range(n):
            drive = real_drive[i] + kappa * internal[i] + inj * feedback[i] * inv_m
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
        self.latent_activity = a_new

        self._write_tissue(drive_out)
        if self.growth_enabled:
            self._grow(a_new, s)

        return {"tick": self.age, "delta": delta, "baseline": self.change_baseline,
                "same_or_different": delta - self.change_baseline}

    # ---- _step_step14
    def _step_step14(self, frame):
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

    # ---- _step_step15
    def _step_step15(self, frame):
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

    # ---- structure_action_lines
    def structure_action_lines(self):
        v = self.structure_action_view()
        out = []
        if not v["structures_formed_now"]:
            out.append("no Structure MSIU formed is being answered with now, so "
                       "the action is read off the activity, as it always was")
            return out
        out.append("the action is read off what MSIU formed, laid where it "
                   "really is")
        for d in v["what_each_one_is_doing"]:
            out.append("   structure #%d  is doing %+.9f  on channels %s"
                       % (d["structure"], d["form"],
                          "  ".join("ch%d" % c for c in d["on_channels"])
                          or "(none)"))
        out.append("   the frame that makes: %s   (of %d channels)"
                   % ("  ".join("%+.6f" % x for x in v["the_frame_they_make"]),
                      len(v["the_frame_they_make"])))
        out.append("   out of which, through the Life's own entry: %s"
                   % ("  ".join("%+.6f" % x
                                for x in v["the_activity_that_comes_of_it"])))
        out.append("   the action: %s"
                   % "  ".join("%+.6f" % x for x in v["the_action"]))
        out.append("   and without a formed Structure it would have been: %s"
                   % "  ".join("%+.6f" % x for x in v["the_action_without_one"]))
        return out

    # ---- structure_action_view
    def structure_action_view(self):
        """What the action is coming from right now, read as it is."""
        formed = self.structures_msiu_formed_now()
        frame = self.structure_frame()
        src = self.structure_source()
        return {
            "enabled": bool(self.structure_action_enabled),
            "structures_formed_now": list(formed),
            "what_each_one_is_doing": [
                {"structure": i,
                 "form": round(self.st_form[i], 9),
                 "on_channels": self.structure_reach(i)} for i in formed],
            "the_frame_they_make": [round(v, 9) for v in frame],
            "the_activity_that_comes_of_it": [round(v, 9) for v in src],
            "from_a_formed_structure": bool(formed) and _norm(src) > 1e-12,
            "the_action": [round(v, 9) for v in self.action()],
            "the_action_without_one": [
                round(v, 9) for v in self._action_step2()],
            "how_deep_they_reach": self.structure_depth(),
        }

    # ---- structure_depth
    def structure_depth(self):
        """How deep the formed Structures' elements reach, for the reading."""
        base = self._base_units()
        worst = 0
        for i in range(len(self.st_ids)):
            for e in self.st_ends[i]:
                depth = 1
                seen, stack = set(), list(self.el_ends[e])
                while stack:
                    u = stack.pop()
                    if u < base:
                        continue
                    j = self.structure_of_unit(u)
                    if j < 0 or j in seen:
                        continue
                    seen.add(j)
                    depth += 1
                    for e2 in self.st_ends[j]:
                        stack.extend(list(self.el_ends[e2]))
                worst = max(worst, depth)
        return worst

    # ---- _structure_depth_step1
    def _structure_depth_step1(self):
        """How deep the formed Structures' elements reach, for the reading.

        A Structure whose elements are made of channels reads 1; one whose
        elements are made of another Structure reads further.  This is only ever
        read out, never used to decide anything.
        """
        ch = self._channels()
        worst = 0
        for i in range(len(self.st_ids)):
            for e in self.st_ends[i]:
                depth = 1
                seen, stack = set(), list(self.el_ends[e])
                while stack:
                    u = stack.pop()
                    if u < ch:
                        continue
                    j = self.structure_of_unit(u)
                    if j < 0 or j in seen:
                        continue
                    seen.add(j)
                    depth += 1
                    for e2 in self.st_ends[j]:
                        stack.extend(list(self.el_ends[e2]))
                worst = max(worst, depth)
        return worst

    # ---- structure_frame
    def structure_frame(self):
        """What the formed Structures are doing, laid where they really are.

        The frame is as wide as the units that are not made of anything, so what
        a Structure is doing can be laid on the Life unit as well as on a
        channel.  The way out reads the reality's own width off it, exactly as it
        always did: the Life unit is not a channel of the reality, and nothing
        laid there is addressed to the reality.
        """
        n = self._base_units()
        frame = [0.0] * n
        for i in self.structures_msiu_formed_now():
            v = self.st_form[i]
            for c in self.structure_reach(i):
                if c < n:
                    frame[c] += v
        return frame

    # ---- _structure_frame_step1
    def _structure_frame_step1(self):
        """What the formed Structures are doing, laid where they really are.

        A frame is read as one value a channel, and a Structure's own form is
        held in the same units as a channel's value, so what a Structure is doing
        can be laid on the channels it is really on.  Where two formed Structures
        are on the same channel both of them are acting there, and both are
        counted.
        """
        frame = [0.0] * self._channels()
        for i in self.structures_msiu_formed_now():
            v = self.st_form[i]
            for c in self.structure_reach(i):
                frame[c] += v
        return frame

    # ---- structure_of_unit
    def structure_of_unit(self, unit):
        """Which Structure a slot stands for, or -1 when it stands for
        something else.  A channel, the Life, and a run's slot are all -1.
        """
        if not getattr(self, "past_run_enabled", False):
            k = unit - self._base_units()
            return k if 0 <= k < len(self.st_ids) else -1
        k = unit - self._base_units()
        if 0 <= k < len(self.unit_kind) and self.unit_kind[k] == "s":
            return self.unit_ref[k]
        return -1

    # ---- _structure_of_unit_step1
    def _structure_of_unit_step1(self, unit):
        """Which Structure a slot stands for, or -1 when it is not a slot.

        A channel, and the Life unit, are not Structures: neither is made of
        anything, and neither is ever given a slot by this implementation.
        """
        k = unit - self._base_units()
        return k if 0 <= k < len(self.st_ids) else -1

    # ---- _structure_of_unit_step2
    def _structure_of_unit_step2(self, unit):
        """Which Structure a slot stands for, or -1 when it is a channel.

        Read off the slot's place and nothing else: there is no table of levels,
        because there are no levels to keep.
        """
        k = unit - self._channels()
        return k if 0 <= k < len(self.st_ids) else -1

    # ---- structure_reach
    def structure_reach(self, i):
        """The channels a formed Structure is really on."""
        out = []
        for e in self.st_ends[i]:
            for c in self.element_reach(e):
                if c not in out:
                    out.append(c)
        return sorted(out)

    # ---- structure_source
    def structure_source(self):
        """What the formed Structure is doing, in the activity the Life runs on.

        The passage from a frame to internal activity is the Life's own innate
        one -- the same one every reality frame goes through.  Nothing new is
        added between a Structure and the way out.
        """
        return self._base_dna.entry_drive(self.structure_frame())

    # ---- structures_msiu_formed_now
    def structures_msiu_formed_now(self):
        """The Structures MSIU has formed and is answering with, now.

        Read off MSIU's own records and nothing else: a Structure it forms for a
        Connection that is still mismatched or broken.  Nothing is chosen,
        ranked or preferred here -- if MSIU is answering with more than one,
        they are all of them.
        """
        out = []
        for i in range(len(self.ms_conn)):
            if not self.ms_current[i]:
                continue
            s = self.ms_structure[i]
            if s >= 0 and s not in out:
                out.append(s)
        return out

    # ---- structures_with_rebuilding
    def structures_with_rebuilding(self):
        """Which Structures have a Connection in a state against them, and which do not.

        A Structure whose connections are all stable has none; one that has a
        mismatched or a broken connection is read off that connection.
        Read from the same tables, so it cannot disagree with msiu_now().
        """
        by = {}
        for k, sid in self.sf_born_in.items():
            if sid < 0:
                continue
            by.setdefault(sid, {"stable": [], "mismatch": [], "broken": []})
            st = self.sf_state.get(k, STABLE)
            by[sid][STATE_NAMES[st]].append(k)
        out = []
        for sid in sorted(by):
            d = by[sid]
            out.append({
                "structure": sid,
                "stable": d["stable"], "mismatch": d["mismatch"],
                "broken": d["broken"],
                "rebuilt": [n["identity"] for n in self.msiu_now()
                          if n["in_structure"] == sid],
                "asks_for_change": bool(d["mismatch"] or d["broken"]),
            })
        return out

    # ---- taking_part
    def taking_part(self, word):
        """The four layers, read off the base's own tables, for this moment."""
        u = self.word_unit(word)
        out = {"age": self.age, "unit": u, "cell": self.word_cell(word),
               "conn": [], "acting": [], "el": [], "st": [], "run": []}
        if u < 0:
            return out
        acting = []
        for k in range(len(self.cn_pre)):
            if self.cn_pre[k] != u and self.cn_post[k] != u:
                continue
            row = {"k": k, "live": self.cn_live[k], "born": self.cn_born[k],
                   "run": self.sf_run.get(k)}
            out["conn"].append(row)
            if self.cn_live[k] >= self._own_conn_bar():
                acting.append(row)
        out["acting"] = acting
        formed = self.formed_now()
        out["el"] = sorted({i for i, words in formed if word in words})
        if out["el"]:
            taken = set(out["el"])
            for i in range(len(self.st_ids)):
                if taken & set(self.st_ends[i]):
                    out["st"].append(i)
        ids = [r["k"] for r in acting]
        for e, ks in enumerate(self.rn_by):
            if self.rn_on[e] and any(x in ids for x in ks):
                out["run"].append({"e": e, "carries": self.rn_form[e],
                                   "brought": self.rn_brought[e]})
        out["in_now"] = bool(out["acting"] or out["el"] or out["st"])
        return out

    # ---- taking_part_now
    def taking_part_now(self, words):
        """Which of these forms are really taking part on this moment."""
        return sorted(w for w in words if self.taking_part(w)["in_now"])

    # ---- thought_has_result
    def thought_has_result(self):
        """Whether a thinking result has really formed and stopped growing."""
        return bool(self.thought_enabled
                    and self.thought_finished_at is not None
                    and self.thought_updates > 0)

    # ---- thought_norm
    def thought_norm(self):
        return math.sqrt(sum(v * v for row in self.thought_coupling for v in row))

    # ---- thought_source
    def thought_source(self):
        """What the thinking result is bringing into the activity right now.

        The thinking result is the coupling that grew inside consciousness.  What
        it is doing at this moment is what it makes of the activity that is
        running now -- the same thing that goes back into the run while thinking
        is going on.
        """
        dna = self._base_dna
        m, n = dna.latent_count, dna.state_size
        T = self.thought_coupling
        a = self.latent_activity
        src = [0.0] * n
        for j in range(m):
            aj = a[j]
            if aj == 0.0:
                continue
            row = T[j]
            for i in range(n):
                src[i] += row[i] * aj
        return src

    # ---- thought_state
    def thought_state(self):
        return {"norm": self.thought_norm(), "updates": self.thought_updates,
                "growing": self.thought_growing,
                "finished_at": self.thought_finished_at,
                "enabled": self.thought_enabled}

    # ---- _thought_state_step1
    def _thought_state_step1(self):
        return {"norm": self.thought_norm(), "updates": self.thought_updates,
                "enabled": self.thought_enabled}

    # ---- tissue_norm
    def tissue_norm(self) -> float:
        return math.sqrt(sum(v * v for v in self.tissue))

    # ---- tissue_profile
    def tissue_profile(self):
        return [1.0 + self.dna.mode_amp * math.tanh(v) for v in self.tissue]

    # ---- touch_traces
    def touch_traces(self, s):
        """The trunk's own recall, and what this Life has already formed.

        The recall is the memory layer together with the addressing it carries,
        and what the Life has already formed comes out of that same running, in
        `_cog_step`.  Nothing is added on top of it: the whole-of-relations layer
 was a second Structure logic beside this Life's own, and it is
        not part of this Life (see `_str_rebuild_index`).
        """
        return self._touch_traces_step1(s)

    # ---- _touch_traces_step1
    def _touch_traces_step1(self, s):
        """The trunk's own recall (memory plus addressing), then the base."""
        inj, ret_w, ret_g = _addressed_touch(self, s)
        if self.cognition_enabled:
            self._cog_step()
        return inj, ret_w, ret_g

    # ---- trace_count_active
    def trace_count_active(self):
        return len(self.trace_keys)

    # ---- trace_pair_cos
    def trace_pair_cos(self, a, b):
        return self._dot(self.trace_keys[a], self.trace_keys[b])

    # ---- update_traces
    def update_traces(self, s, w, g):
        dna = self.dna
        if not self.trace_enabled:
            return
        sh = self._shape(s)
        if sh is None:
            return
        if not self.trace_shaping_enabled:
            for j, wj in enumerate(w):
                if wj > 0.0:
                    self.trace_used[j] += 1
            w = [0.0] * len(w)
        nu = dna.trace_rate
        nuk = dna.trace_key_rate
        for j, wj in enumerate(w):
            if wj <= 0.0:
                continue
            if nuk > 0.0:
                k = self.trace_keys[j]
                nk = [(1.0 - nuk) * k[i] + nuk * sh[i] for i in range(len(sh))]
                unit = self._shape(nk)
                if unit is not None:
                    self.trace_keys[j] = unit
            if nu > 0.0:
                m = self.trace_cont[j]
                self.trace_cont[j] = [(1.0 - nu) * m[i] + nu * s[i] for i in range(len(s))]
            self.trace_used[j] += 1

        if not self.trace_formation_enabled:
            return
        if len(self.trace_keys) >= dna.trace_count:
            return
        top = max(g) if g else None
        if top is not None and top >= dna.trace_form_match:
            return
        if (self.age - self.last_trace_age) < dna.trace_refractory:
            return
        self.trace_keys.append(list(sh))
        self.trace_cont.append(list(s))
        self.trace_born.append(self.age)
        self.trace_used.append(0)
        self.last_trace_age = self.age

    # ---- update_traces_split
    def update_traces_split(self, cue_src, content_src, w, g):
        dna = self.dna
        if not self.trace_enabled:
            return
        sh = self._shape(cue_src)
        if sh is None:
            return
        if not self.trace_shaping_enabled:
            for j, wj in enumerate(w):
                if wj > 0.0:
                    self.trace_used[j] += 1
            w = [0.0] * len(w)
        nu = dna.trace_rate
        nuk = dna.trace_key_rate
        for j, wj in enumerate(w):
            if wj <= 0.0:
                continue
            if nuk > 0.0:
                k = self.trace_keys[j]
                nk = [(1.0 - nuk) * k[i] + nuk * sh[i] for i in range(len(sh))]
                unit = self._shape(nk)
                if unit is not None:
                    self.trace_keys[j] = unit
            if nu > 0.0:
                m = self.trace_cont[j]
                self.trace_cont[j] = [(1.0 - nu) * m[i] + nu * content_src[i]
                                      for i in range(len(content_src))]
            self.trace_used[j] += 1

        if not self.trace_formation_enabled:
            return
        if len(self.trace_keys) >= dna.trace_count:
            return
        top = max(g) if g else None
        if top is not None and top >= dna.trace_form_match:
            return
        if (self.age - self.last_trace_age) < dna.trace_refractory:
            return
        self.trace_keys.append(list(sh))
        self.trace_cont.append(list(content_src))
        self.trace_born.append(self.age)
        self.trace_used.append(0)
        self.last_trace_age = self.age

    # ---- walk_note
    def walk_note(self, i):
        """One Structure's own members, kept so a later move can be traced."""
        for e in self.st_ends[i]:
            self.walk_el_st.setdefault(e, set()).add(i)

    # ---- walk_wrap
    def walk_wrap(self):
        """Keep the three noted lists noted, however the Life was made.

        A Life read back from a dump has these tables as plain lists of the same
        values.  Wrapping one again changes no value, no length and no order.
        """
        if not isinstance(self.st_frames, Running):
            self.st_frames = Running(self.st_frames)
        if not isinstance(self.el_ends, Growing):
            self.el_ends = Growing(self.el_ends)
        if not isinstance(self.st_ends, Growing):
            self.st_ends = Growing(self.st_ends)

    # ---- who
    def who(self, unit):
        """Which participant this end belongs to.

        A port answers with the Life; every other end answers with itself, which
        is what "one end owns itself" means for the ends that always stood for
        one participant each.
        """
        return self.ow_owner.get(unit, unit)

    # ---- word_at
    def word_at(self, u):
        """The form a place stands for, or None -- read off the base's own tables."""
        k = u - self._base_units()
        if 0 <= k < len(self.unit_kind) and self.unit_kind[k] == WORD_KIND:
            ref = self.unit_ref[k]
            if 0 <= ref < len(self.wd_order):
                return self.wd_order[ref]
        return None

    # ---- word_cell
    def word_cell(self, name):
        """What the form's own place carries right now, read off the one list."""
        u = self.word_unit(name)
        if u < 0 or not self.frame_now or u >= len(self.frame_now):
            return None
        return self.frame_now[u]

    # ---- word_connections
    def word_connections(self):
        """Every Connection the base really issued that has a form for an end.

        Read off `cn_pre` / `cn_post` / `cn_live` -- the base's own tables.  A
        Connection exists here only because the base's own judgement issued it.
        """
        out = []
        for k in range(len(self.cn_pre)):
            a, b = self.cn_pre[k], self.cn_post[k]
            wa, wb = self.word_at(a), self.word_at(b)
            if wa is None and wb is None:
                continue
            out.append({"k": k, "pre": a, "post": b, "wa": wa, "wb": wb,
                        "born": self.cn_born[k], "live": self.cn_live[k],
                        "peak": self.cn_peak[k]})
        return out

    # ---- word_elements
    def word_elements(self):
        """Every Element the base really formed that holds a form."""
        out = []
        for e in range(len(self.el_ends)):
            words = sorted({self.word_at(u) for u in self.el_ends[e]
                            if self.word_at(u) is not None})
            if words:
                out.append({"e": e, "words": words,
                            "members": [self.end_label(u) for u in self.el_ends[e]]})
        return out

    # ---- word_present
    def word_present(self, name):
        return self.wd_now.get(name, 0.0) > 0.0

    # ---- word_structures
    def word_structures(self):
        """Every Structure the base really formed that holds a form."""
        out = []
        for i in range(len(self.st_ids)):
            members = [self.end_label(u)
                       for e in self.st_ends[i] for u in self.el_ends[e]]
            words = sorted({self.word_at(u) for e in self.st_ends[i]
                            for u in self.el_ends[e]
                            if self.word_at(u) is not None})
            if words:
                out.append({"i": i, "words": words, "members": sorted(set(members)),
                            "edges": len(self.st_edges[i])})
        return out

    # ---- word_unit
    def word_unit(self, name):
        """Where a form sits in the one list, or -1 when it has never appeared."""
        return self.wd_unit.get(name, -1)

    # ---- words_present
    def words_present(self):
        return [n for n, v in self.wd_now.items() if v > 0.0]


# ==== the state file

def dump_life_step0(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life.dna).items()},
        "life": {f: getattr(life, f) for f in V07_FIELDS},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step1(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life.dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_11},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step2(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_12},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step3(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_13},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step4(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_14},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step5(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_15},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step6(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_16},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step7(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_17},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "memory": {f: getattr(life, f) for f in MEMORY_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step8(life, path, meta=None):
    payload = {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_18},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "memory": {f: getattr(life, f) for f in MEMORY_FIELDS},
        "meta": meta or {},
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step9(life, path, meta=None):
    payload = _trunk_sections(life, meta=meta)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

def dump_life_step17(life, path, meta=None):
    """The trunk writes itself exactly as before, then the organ's part is added.

    The trunk's sections are left as the trunk wrote them; the organ's own
    experience is put in beside them, in its own section, so that it is read back
    with the Life rather than held only by the running.  The top-level `format`
    is set to this implementation, because the file now holds a section the trunk does
    not write.  Nothing is validated on the way in, and no older file is touched.
    """
    dump_life_step9(life, path, meta=meta)
    with io.open(path, "r", encoding="utf-8") as f:
        payload = json.load(f)
    payload[EXPRESSION_SECTION] = life.expression_memory()
    payload["format"] = STATE_FORMAT
    with io.open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False)
    return path

_trunk_dump = dump_life_step17


def load_life_step0(path, inlet=None):
    payload = _read_payload(path)

    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k in DNA_TUPLE_FIELDS:
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet)
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    return life, payload.get("meta", {})

def load_life_step1(path, inlet=None):
    payload = _read_payload(path)

    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k in DNA_TUPLE_FIELDS:
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet)
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    return life, payload.get("meta", {})

def load_life_step2(path, inlet=None):
    payload = _read_payload(path)

    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k in DNA_TUPLE_FIELDS:
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if "source_weights" not in payload["dna"]:
        sd = int(getattr(dna, "source_dim", SOURCE_DIM))
        dna.source_dim = sd
        dna.source_weights, dna.source_scale, dna.source_seed = make_source_weights(dna, sd)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet)
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    if "last_cue" in payload:
        life.last_cue = _plain(payload["last_cue"])
    life._frame_source = [0.0] * life.source_dim
    return life, payload.get("meta", {})

def load_life_step3(path, inlet=None):
    payload = _read_payload(path)

    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k in ("_kernel_offsets",):
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if "source_weights" not in payload["dna"]:
        sd = int(getattr(dna, "source_dim", SOURCE_DIM))
        dna.source_dim = sd
        dna.source_weights, dna.source_scale, dna.source_seed = make_source_weights(dna, sd)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet)
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    if "last_cue" in payload:
        life.last_cue = _plain(payload["last_cue"])
    life._frame_source = [0.0] * life.source_dim
    life.conscious_flow = [0.0] * dna.state_size
    life.conscious_ticks = 0
    life.conscious_active = False
    return life, payload.get("meta", {})

def load_life_step4(path, inlet=None):
    payload = _read_payload(path)

    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k == "_kernel_offsets":
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if "source_weights" not in payload["dna"]:
        sd = int(getattr(dna, "source_dim", SOURCE_DIM))
        dna.source_dim = sd
        dna.source_weights, dna.source_scale, dna.source_seed = make_source_weights(dna, sd)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet)
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    if "last_cue" in payload:
        life.last_cue = _plain(payload["last_cue"])
    life._frame_source = [0.0] * life.source_dim
    life.conscious_flow = [0.0] * dna.state_size
    life.conscious_ticks = 0
    life.conscious_active = False
    life.thought_coupling = [[0.0] * dna.state_size for _ in range(dna.latent_count)]
    life.thought_updates = 0
    return life, payload.get("meta", {})

def load_life_step5(path, inlet=None):
    payload = _read_payload(path)

    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k == "_kernel_offsets":
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if "source_weights" not in payload["dna"]:
        sd = int(getattr(dna, "source_dim", SOURCE_DIM))
        dna.source_dim = sd
        dna.source_weights, dna.source_scale, dna.source_seed = make_source_weights(dna, sd)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet)
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    if "last_cue" in payload:
        life.last_cue = _plain(payload["last_cue"])
    life._frame_source = [0.0] * life.source_dim
    life.conscious_flow = [0.0] * dna.state_size
    life.conscious_ticks = 0
    life.conscious_active = False
    life.thought_coupling = [[0.0] * dna.state_size for _ in range(dna.latent_count)]
    life.thought_updates = 0
    life.last_internal_trace_w = []
    life.last_internal_trace_in = [0.0] * dna.state_size
    life.last_trace_in_old = [0.0] * dna.state_size
    return life, payload.get("meta", {})

def load_life_step6(path, inlet=None):
    payload = _read_payload(path)

    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k == "_kernel_offsets":
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if "source_weights" not in payload["dna"]:
        sd = int(getattr(dna, "source_dim", SOURCE_DIM))
        dna.source_dim = sd
        dna.source_weights, dna.source_scale, dna.source_seed = make_source_weights(dna, sd)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet)
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    if "last_cue" in payload:
        life.last_cue = _plain(payload["last_cue"])
    life._frame_source = [0.0] * life.source_dim
    life.conscious_flow = [0.0] * dna.state_size
    life.conscious_ticks = 0
    life.conscious_active = False
    life.thought_coupling = [[0.0] * dna.state_size for _ in range(dna.latent_count)]
    life.thought_updates = 0
    life.thought_growing = False
    life.thought_finished_at = None
    life.last_internal_trace_w = []
    life.last_internal_trace_in = [0.0] * dna.state_size
    life.last_trace_in_old = [0.0] * dna.state_size
    return life, payload.get("meta", {})

def load_life_step7(path, inlet=None):
    payload = _read_payload(path)

    mem = payload.get("memory", {})
    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k == "_kernel_offsets":
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if "source_weights" not in payload["dna"]:
        sd = int(getattr(dna, "source_dim", SOURCE_DIM))
        dna.source_dim = sd
        dna.source_weights, dna.source_scale, dna.source_seed = make_source_weights(dna, sd)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet, memory_enabled=bool(mem.get("memory_enabled", True)))
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    if "last_cue" in payload:
        life.last_cue = _plain(payload["last_cue"])

    # The memory layer holds no relations of its own: a relation is a
    # Connection, and what stands beside the Connections -- how much each is in
    # play, the moments each was really continued, the experience each came
    # about in -- is history, and comes back with the history
    # (`_restore_history`).  What is read here is the continuity, and the switch.
    life.bar_d = _plain(mem["bar_d"]) if "bar_d" in mem else [0.0] * dna.state_size
    life.mem_prev_u = None
    life.mem_inj_prev = None
    life.mem_last_u = None
    life.mem_coeff, life.mem_g_last = {}, []
    life._mem_part_last, life._mem_part_now = {}, {}
    life.mem_active_touched = life.mem_active_computed = life.mem_active_fired = 0
    life.mem_active_fireable = 0
    life.mem_active_set = []
    life.mem_fired_last = ()
    life.mem_frames = life.mem_recognized = 0
    life._mem_have_input = False
    if life.memory_enabled:
        life._detach_old_trace_layer()

    life._frame_source = [0.0] * life.source_dim
    life.conscious_flow = [0.0] * dna.state_size
    life.conscious_ticks = 0
    life.conscious_active = False
    life.thought_coupling = [[0.0] * dna.state_size for _ in range(dna.latent_count)]
    life.thought_updates = 0
    life.thought_growing = False
    life.thought_finished_at = None
    life.last_internal_trace_w = []
    life.last_internal_trace_in = [0.0] * dna.state_size
    life.last_trace_in_old = [0.0] * dna.state_size
    return life, payload.get("meta", {})

def load_life_step8(path, inlet=None):
    payload = _read_payload(path)

    mem = payload.get("memory", {})
    dna = LifeDNA()
    for k, v in payload["dna"].items():
        if k == "_kernel_offsets":
            v = [tuple(x) for x in v]
        setattr(dna, k, v)
    if "source_weights" not in payload["dna"]:
        sd = int(getattr(dna, "source_dim", SOURCE_DIM))
        dna.source_dim = sd
        dna.source_weights, dna.source_scale, dna.source_seed = make_source_weights(dna, sd)
    if inlet is None:
        inlet = RealityInlet(dna.channel_count)

    life = LifeGrowth(dna, inlet, memory_enabled=bool(mem.get("memory_enabled", True)))
    for f, v in payload.get("life", {}).items():
        setattr(life, f, _plain(v))
    for f, v in payload.get("trace", {}).items():
        setattr(life, f, _plain(v))
    if "last_cue" in payload:
        life.last_cue = _plain(payload["last_cue"])

    life.bar_d = _plain(mem["bar_d"]) if "bar_d" in mem else [0.0] * dna.state_size
    life.mem_prev_u = None
    life.mem_inj_prev = None
    life.mem_coeff, life.mem_g_last = {}, []
    life._mem_part_now = {}
    life._mem_have_input = False
    life.mem_active_set = []
    life.mem_fired_last = ()
    life.mem_last_recognized = -1
    life.mem_search_size = 0
    life.mem_flow_size = 0
    life.mem_frames = life.mem_recognized = 0
    life.mem_active_touched = life.mem_active_computed = 0
    life.mem_active_fireable = life.mem_active_fired = 0
    life.mem_front = []
    if life.memory_enabled:
        life._detach_old_trace_layer()

    life._frame_source = [0.0] * life.source_dim
    life.conscious_flow = [0.0] * dna.state_size
    life.conscious_ticks = 0
    life.conscious_active = False
    life.thought_coupling = [[0.0] * dna.state_size for _ in range(dna.latent_count)]
    life.thought_updates = 0
    life.thought_growing = False
    life.thought_finished_at = None
    life.last_internal_trace_w = []
    life.last_internal_trace_in = [0.0] * dna.state_size
    life.last_trace_in_old = [0.0] * dna.state_size
    return life, payload.get("meta", {})

def load_life_step9(path, inlet=None):
    life, meta = load_life_step8(path, inlet)
    payload = _read_payload(path)
    out = LifeGrowth(life._base_dna, life.inlet,
                       memory_enabled=life.memory_enabled,
                       structure_enabled=life.structure_enabled if hasattr(life, "structure_enabled") else True)
    for k, v in vars(life).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        setattr(out, k, v)
    out.dna = life.dna
    return out, meta

def load_life_step10(path, inlet=None, address_enabled=True):
    base, meta = load_life_step9(path, inlet)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       structure_enabled=base.structure_enabled,
                       address_enabled=address_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna") or k.startswith("addr_"):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    # the switch is set after the copy, because the copy carries it over
    out.address_enabled = bool(address_enabled)
    out._str_rebuild_index()
    out._end_align()
    return out, meta

def load_life_step11(path, inlet=None, address_enabled=True, cognition_enabled=True):
    base, meta = load_life_step10(path, inlet, address_enabled=address_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "frame_now")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out._str_rebuild_index()
    out._end_align()
    return out, meta

def load_life_step12(path, inlet=None, address_enabled=True, cognition_enabled=True):
    base, meta = load_life_step11(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "frame_now")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out._str_rebuild_index()
    out._end_align()
    return out, meta

def load_life_step13(path, inlet=None, address_enabled=True, cognition_enabled=True):
    base, meta = load_life_step12(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "frame_now")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out._str_rebuild_index()
    out._end_align()
    return out, meta

def load_life_step14(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True):
    base, meta = load_life_step13(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "frame_now")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out._str_rebuild_index()
    out._end_align()
    return out, meta

def load_life_step15(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True):
    base, meta = load_life_step14(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "frame_now")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out._str_rebuild_index()
    out._end_align()
    return out, meta

def load_life_step16(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True):
    base, meta = load_life_step15(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out._str_rebuild_index()
    out._end_align()
    return out, meta

def load_life_step17(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True):
    """Read the Life back, and the organ's own experience with it.

    The organ's section is read first and kept on its own, so that only one copy
    of the file is ever held at a time; then the trunk loads exactly as 
    loads it, and the organ's experience is put back on the new organ.
    """
    payload = _read_payload(path)
    learned = payload.get(EXPRESSION_SECTION) or {}
    del payload

    base, meta = load_life_step16(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ, and nothing else
    out.expression_restore(learned)
    return out, meta

def load_life_step18(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True):
    base, meta = load_life_step17(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step19(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True):
    base, meta = load_life_step18(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step20(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True):
    base, meta = load_life_step19(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step21(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True):
    base, meta = load_life_step20(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step22(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True):
    base, meta = load_life_step21(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step23(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True):
    base, meta = load_life_step22(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step24(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True):
    base, meta = load_life_step23(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step25(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True):
    base, meta = load_life_step24(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step26(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False):
    base, meta = load_life_step25(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_", "unit_", "pr_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step27(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False):
    base, meta = load_life_step26(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_", "unit_", "pr_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step28(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False,
                past_structure_enabled=True):
    base, meta = load_life_step27(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all,
                       past_structure_enabled=past_structure_enabled)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_", "unit_", "pr_",
                         "past_structure_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out.past_structure_enabled = bool(past_structure_enabled)
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step29(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False,
                past_structure_enabled=True, behavior_count=BEHAVIOR_CHANNELS):
    base, meta = load_life_step28(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all,
                             past_structure_enabled=past_structure_enabled)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all,
                       past_structure_enabled=past_structure_enabled,
                       behavior_count=behavior_count)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_", "unit_", "pr_",
                         "past_structure_", "bh_", "behavior_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out.past_structure_enabled = bool(past_structure_enabled)
    out.behavior_count = int(behavior_count)
    out.bh_now = [0.0] * out.behavior_count
    out.bh_set_moments = 0
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step30(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False,
                past_structure_enabled=True, behavior_count=BEHAVIOR_CHANNELS):
    base, meta = load_life_step29(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all,
                             past_structure_enabled=past_structure_enabled,
                             behavior_count=behavior_count)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all,
                       past_structure_enabled=past_structure_enabled,
                       behavior_count=behavior_count)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_", "unit_", "pr_",
                         "past_structure_", "bh_", "behavior_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out.past_structure_enabled = bool(past_structure_enabled)
    out.behavior_count = int(behavior_count)
    out.bh_now = [0.0] * out.behavior_count
    out.bh_set_moments = 0
    out._str_rebuild_index()
    out._end_align()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step31(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False,
                past_structure_enabled=True, behavior_count=BEHAVIOR_CHANNELS):
    """Read a Life back, with the current layer on its running.

    What comes back is what the trunk and the organ bring back, and this was measured
    rather than assumed: the trunk, the DNA, the organ's own memory and the
    switches -- and **no relation history at all** (a Life that had 25
    connections, 10 elements and 1 structure came back with 0, 0 and 0, and 13
    ends, exactly as the base does; a state file written before this does not carry the
    relation tables).  This implementation does not change that.

    The current layer's own tables come back empty, which is the honest state:
    who is taking part is not stored, it is read off the acting connections from
    the first moment on.
    """
    base, meta = load_life_step30(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all,
                             past_structure_enabled=past_structure_enabled,
                             behavior_count=behavior_count)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all,
                       past_structure_enabled=past_structure_enabled,
                       behavior_count=behavior_count)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "sa_", "lf_", "self_perception_",
                         "rn_", "run_history_", "unit_", "pr_",
                         "past_structure_", "bh_", "behavior_",
                         "join_", "cur_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out.past_structure_enabled = bool(past_structure_enabled)
    out.behavior_count = int(behavior_count)
    out.bh_now = [0.0] * out.behavior_count
    out.bh_set_moments = 0
    out._str_rebuild_index()
    out._end_align()

    # the two switches this implementation adds, and the current layer's own tables
    out.join_on = True
    out.join_zero = True
    out.el_now = []
    out.el_at = {}
    out.cur_el = []
    out.cur_st = []
    out.keep_log = False
    out.join_log = []

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step32(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False,
                past_structure_enabled=True, behavior_count=BEHAVIOR_CHANNELS):
    """Read a Life back, with the act read as a sum.

    What comes back is what the layer below brings back -- the trunk, the DNA, the organ's
    own memory, the switches, and **no relation history at all** (a state file written before this does not carry the relation tables; this implementation does not change
    that), plus one thing of its own: `structure_joins_enabled`, which is set
    **after** the attribute copy and then stands, because that copy would
    otherwise carry the source object's own value over it.
    """
    base, meta = load_life_step31(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all,
                             past_structure_enabled=past_structure_enabled,
                             behavior_count=behavior_count)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all,
                       past_structure_enabled=past_structure_enabled,
                       behavior_count=behavior_count)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "structure_joins_", "sa_", "lf_",
                         "self_perception_", "rn_", "run_history_", "unit_",
                         "pr_", "past_structure_", "bh_", "behavior_",
                         "join_", "cur_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out.past_structure_enabled = bool(past_structure_enabled)
    out.behavior_count = int(behavior_count)
    out.bh_now = [0.0] * out.behavior_count
    out.bh_set_moments = 0
    out._str_rebuild_index()
    out._end_align()

    # switches and its current layer's tables come back as 
    # brings them back
    out.join_on = True
    out.join_zero = True
    out.el_now = []
    out.el_at = {}
    out.cur_el = []
    out.cur_st = []
    out.keep_log = False
    out.join_log = []

    # the switch here: set after the copy, and it stands
    out.structure_joins_enabled = True

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step33(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False,
                past_structure_enabled=True, behavior_count=BEHAVIOR_CHANNELS):
    """Read a Life back, with the judgement kept to the ends taking part now.

    What comes back is what the layer below brings back -- the trunk, the DNA, the organ's
    own memory, the switches, and **no relation history at all** (a state file written before this does not carry the relation tables; this implementation does not change
    that), plus two things of its own: `cn_local_enabled` and `cn_place`, both set
    **after** the attribute copy and then standing, because that copy would
    otherwise carry the source object's own value over them.  `cn_place` comes
    back empty, which is what a place with no past is kept as.
    """
    base, meta = load_life_step32(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all,
                             past_structure_enabled=past_structure_enabled,
                             behavior_count=behavior_count)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all,
                       past_structure_enabled=past_structure_enabled,
                       behavior_count=behavior_count)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "structure_joins_", "sa_", "lf_",
                         "self_perception_", "rn_", "run_history_", "unit_",
                         "pr_", "past_structure_", "bh_", "behavior_",
                         "join_", "cur_")):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out.past_structure_enabled = bool(past_structure_enabled)
    out.behavior_count = int(behavior_count)
    out.bh_now = [0.0] * out.behavior_count
    out.bh_set_moments = 0
    out._str_rebuild_index()
    out._end_align()

    # switches and its current layer's tables come back as 
    # brings them back
    out.join_on = True
    out.join_zero = True
    out.el_now = []
    out.el_at = {}
    out.cur_el = []
    out.cur_st = []
    out.keep_log = False
    out.join_log = []

    # switch, as it brings it back
    out.structure_joins_enabled = True

    # the switch here switch, and the pairs the moment before walked: set after
    # the copy, and they stand
    out.cn_local_enabled = True
    out.cn_place = frozenset()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

def load_life_step34(path, inlet=None, address_enabled=True, cognition_enabled=True,
                state_enabled=True, las_enabled=True, expression_enabled=True,
                recursion_enabled=True, msiu_view_enabled=True,
                msiu_las_view_enabled=True, msiu_enabled=True,
                structure_action_enabled=True, self_perception_enabled=True,
                run_history_enabled=True, sf_run_enabled=True,
                past_run_enabled=True, past_run_all=False,
                past_structure_enabled=True, behavior_count=BEHAVIOR_CHANNELS):
    """Read a Life back, with the history kept as stretches and the list carried.

    What comes back is what the layer below brings back -- the trunk, the DNA, the organ's
    own memory, the switches, and **no relation history at all** (a state file written before this does not carry the relation tables; this implementation does not change
    that), plus the switch here: the four switches the four rounds keep and
    the indices this layer keeps, set **after** the attribute copy and then
    standing, because that copy would otherwise carry the source object's own
    value over them.  Each round's own tables come back as that round brings
    them back -- the count and the two frozen member tables noted by their own
    writing, the three-state history empty, and the one list carried from
    nothing.

    The address space is not built here, and no layer above builds it either:
    it is derived from the relation memory, which is whole by the time
    `load_life` has read the file, and `load_life` builds it once there.
    """
    base, meta = load_life_step33(path, inlet, address_enabled=address_enabled,
                             cognition_enabled=cognition_enabled,
                             state_enabled=state_enabled,
                             las_enabled=las_enabled,
                             expression_enabled=expression_enabled,
                             recursion_enabled=recursion_enabled,
                             msiu_view_enabled=msiu_view_enabled,
                             msiu_las_view_enabled=msiu_las_view_enabled,
                             msiu_enabled=msiu_enabled,
                             structure_action_enabled=structure_action_enabled,
                             self_perception_enabled=self_perception_enabled,
                             run_history_enabled=run_history_enabled,
                             sf_run_enabled=sf_run_enabled,
                             past_run_enabled=past_run_enabled,
                             past_run_all=past_run_all,
                             past_structure_enabled=past_structure_enabled,
                             behavior_count=behavior_count)
    out = LifeGrowth(base._base_dna, base.inlet,
                       memory_enabled=base.memory_enabled,
                       address_enabled=address_enabled,
                       cognition_enabled=cognition_enabled,
                       state_enabled=state_enabled,
                       las_enabled=las_enabled,
                       expression_enabled=expression_enabled,
                       recursion_enabled=recursion_enabled,
                       msiu_view_enabled=msiu_view_enabled,
                       msiu_las_view_enabled=msiu_las_view_enabled,
                       msiu_enabled=msiu_enabled,
                       structure_action_enabled=structure_action_enabled,
                       self_perception_enabled=self_perception_enabled,
                       run_history_enabled=run_history_enabled,
                       sf_run_enabled=sf_run_enabled,
                       past_run_enabled=past_run_enabled,
                       past_run_all=past_run_all,
                       past_structure_enabled=past_structure_enabled,
                       behavior_count=behavior_count)
    for k, v in vars(base).items():
        if k in ("dna", "inlet", "_base_dna"):
            continue
        if k.startswith(("cn_", "ch_", "el_", "st_", "cog_", "sf_", "las_",
                         "expression_", "out_weights", "frame_now",
                         "take_part_", "ms_", "msiu_",
                         "structure_action_", "structure_joins_", "sa_", "lf_",
                         "self_perception_", "rn_", "run_history_", "unit_",
                         "pr_", "past_structure_", "bh_", "behavior_",
                         "join_", "cur_")) or k.startswith("walk"):
            continue
        setattr(out, k, v)
    out.dna = base.dna
    out.address_enabled = bool(address_enabled)
    out.cognition_enabled = bool(cognition_enabled)
    out.state_enabled = bool(state_enabled)
    out.las_enabled = bool(las_enabled)
    out.expression_enabled = bool(expression_enabled)
    out.recursion_enabled = bool(recursion_enabled)
    out.msiu_view_enabled = bool(msiu_view_enabled)
    out.msiu_las_view_enabled = bool(msiu_las_view_enabled)
    out.msiu_enabled = bool(msiu_enabled)
    out.structure_action_enabled = bool(structure_action_enabled)
    out.self_perception_enabled = bool(self_perception_enabled)
    out.run_history_enabled = bool(run_history_enabled)
    out.sf_run_enabled = bool(sf_run_enabled)
    out.past_run_enabled = bool(past_run_enabled)
    out.past_run_all = bool(past_run_all)
    out.past_structure_enabled = bool(past_structure_enabled)
    out.behavior_count = int(behavior_count)
    out.bh_now = [0.0] * out.behavior_count
    out.bh_set_moments = 0
    out._str_rebuild_index()
    out._end_align()

    # switches and its current layer's tables come back as 
    # brings them back
    out.join_on = True
    out.join_zero = True
    out.el_now = []
    out.el_at = {}
    out.cur_el = []
    out.cur_st = []
    out.keep_log = False
    out.join_log = []

    # switch, as it brings it back
    out.structure_joins_enabled = True

    # switch, and the pairs the moment before walked
    out.cn_local_enabled = True
    out.cn_place = frozenset()

    # the switch here: the four switches and every index the four rounds
    # keep, set after the copy, and they stand
    out._start_walks()

    # what the organ really learned comes back on the new organ
    out.expression_restore(base.expression_memory())
    return out, meta

_trunk_load = load_life_step34


# ======================================================================
STATE_FORMAT = "life-growth-state"


def new_life(channel_count=6, behavior_count=BEHAVIOR_CHANNELS,
             expression_enabled=True):
    """A fresh Life: the one class, built the way the formal entry builds it."""
    L = LifeGrowth(LifeDNA(channel_count=channel_count),
                   RealityInlet(channel_count))
    L.behavior_count = int(behavior_count)
    L.bh_now = [0.0] * L.behavior_count
    L.expression_enabled = bool(expression_enabled)
    L.join_on = True
    L.join_zero = True
    L.structure_joins_enabled = True
    L.cn_local_enabled = True
    L.cn_place = frozenset()
    L.now_scope_enabled = True
    L.only_running_enabled = True
    L.sf_runs_enabled = True
    L.sf_wrap()
    L.carry_enabled = True
    L.sp_keep = False
    L.sp_say = []
    return L


# ----------------------------------------------------------------------
# the history that goes into the state file, and what does not
#
# What is carried is what a Life has formed and organised: the identity of
# every Connection it has really issued, the ends it is between, when it came
# about and the highest the reading ever got; the Element identities, their
# members, and which parts each of them has played; the Structure identities,
# their ends and their edges; which runs really happened; and the way each
# Connection was first seen running, which is what the three states are judged
# against.
#
# What is not carried is the running itself: whether each of them is acting on
# this moment, what each Element is reading of its own channels this moment,
# and which of the three states it is in now, are formed again from what really
# happens next (V3.0 2.9).  A Life read back therefore stands its own current
# tables up empty beside the identities that came back, and never invents a
# reading for one: see `_align_now`.
#
# What is carried beside the identities is the scales the Life has read out of
# its own experience, because those cannot be read again out of anything here:
# see `_own_scales_of`.
def _history_of(life):
    return {
        "cn_pre": [int(v) for v in life.cn_pre],
        "cn_post": [int(v) for v in life.cn_post],
        "cn_born": [int(v) for v in life.cn_born],
        "cn_peak": [float(v) for v in life.cn_peak],
        "cn_way": [float(v) for v in getattr(life, "cn_way", [])],
        "cn_key": [[float(x) for x in row]
                   for row in getattr(life, "cn_key", [])],
        # what the memory keeps for each relation: how much it is in play, and
        # the moments it was really continued.  There is one relation table and
        # it is the Connections', so these stand beside the history above.
        "mem_s": [float(v) for v in getattr(life, "mem_s", [])],
        "mem_hit": [int(v) for v in getattr(life, "mem_hit", [])],
        "el_ends": [list(t) for t in life.el_ends],
        "el_born": [int(v) for v in getattr(life, "el_born", [])],
        "el_frames": [int(v) for v in getattr(life, "el_frames", [])],
        "el_sides": [sorted(int(s) for s in v)
                     for v in getattr(life, "el_sides", [])],
        "st_ids": [int(v) for v in life.st_ids],
        "st_ends": [list(t) for t in life.st_ends],
        "st_edges": [list(t) for t in life.st_edges],
        "st_born": [int(v) for v in getattr(life, "st_born", [])],
        "st_frames": [int(v) for v in life.st_frames],
        "rn_start": [int(v) for v in getattr(life, "rn_start", [])],
        "rn_stop": [None if v is None else int(v)
                    for v in getattr(life, "rn_stop", [])],
        "rn_struct": [int(v) for v in getattr(life, "rn_struct", [])],
        "sf_way": dict((str(k), int(v)) for k, v in life.sf_way.items()),
        "sf_born_in": dict((str(k), int(v)) for k, v in life.sf_born_in.items()),
        "sf_frames": dict(("%s|%s" % (k[0], k[1]), int(v))
                          for k, v in life.sf_frames.items()),
        # the states themselves, and the identity every place stands for: the
        # running layer cannot rebuild these, so they go in as they stand
        "sf_state": dict((str(k), int(v)) for k, v in life.sf_state.items()),
        "sf_run": dict((str(k), int(v))
                       for k, v in getattr(life, "sf_run", {}).items()),
        "unit_kind": [str(v) for v in getattr(life, "unit_kind", [])],
        "unit_ref": [int(v) for v in getattr(life, "unit_ref", [])],
        "st_unit": [int(v) for v in getattr(life, "st_unit", [])],
        "st_form": [float(v) for v in getattr(life, "st_form", [])],
        "st_run_open": [int(v) for v in getattr(life, "st_run_open", [])],
        "rn_unit": [int(v) for v in getattr(life, "rn_unit", [])],
        "rn_form": [float(v) for v in getattr(life, "rn_form", [])],
        "rn_on": [bool(v) for v in getattr(life, "rn_on", [])],
        "rn_by": [sorted(int(x) for x in v)
                  for v in getattr(life, "rn_by", [])],
        "rn_brought": [int(v) for v in getattr(life, "rn_brought", [])],
        "rn_epi": [[[int(a), None if b is None else int(b)] for a, b in ep]
                   for ep in getattr(life, "rn_epi", [])],
        "rn_epi_open": [bool(v) for v in getattr(life, "rn_epi_open", [])],
        "rn_ord": [int(v) for v in getattr(life, "rn_ord", [])],
        "wd_order": [str(v) for v in getattr(life, "wd_order", [])],
        "wd_unit": dict((str(a), int(b))
                        for a, b in getattr(life, "wd_unit", {}).items()),
        "wd_seen": dict((str(a), int(b))
                        for a, b in getattr(life, "wd_seen", {}).items()),
        "wd_born": dict((str(a), int(b))
                        for a, b in getattr(life, "wd_born", {}).items()),
        # The scales this Life has itself read, and cannot read again out of the
        # history above: the smallest manner it has formed a Connection at, the
        # weakest share it has held one of its own relations at while it still
        # held, and the matches it has read.  They are what it judges the very
        # next moment by, so they travel here with the history and come back
        # exactly as they stood.
        "own_form_lo": (None if getattr(life, "own_form_lo", None) is None
                        else float(life.own_form_lo)),
        "own_break_share": float(getattr(life, "own_break_share", 1.0)),
        "mem_g_sum": float(getattr(life, "mem_g_sum", 0.0)),
        "mem_g_n": int(getattr(life, "mem_g_n", 0)),
    }


def _own_scales_of(life, d):
    """The scales this Life has itself read, put back exactly as they stood.

    None of these can be read again out of the history: `own_form_lo` is the
    smallest manner this Life has formed one of its own Connections at,
    `own_break_share` how far its own relations have been seen to fall while
    still holding, and the two `mem_g_*` how close the matches it has read
    stood.  A life read back therefore judges its very next moment by the very
    numbers it was judging by when it was written.

    Called after the walks have been stood up, because standing them up puts a
    fresh Life's own defaults in these places.  A state file from before these
    were carried leaves them as those defaults, which is the truth about that
    life: it had never read them.
    """
    if not d:
        return
    if "own_form_lo" in d:
        v = d["own_form_lo"]
        life.own_form_lo = None if v is None else float(v)
    if "own_break_share" in d:
        life.own_break_share = float(d["own_break_share"])
    if "mem_g_sum" in d:
        life.mem_g_sum = float(d["mem_g_sum"])
    if "mem_g_n" in d:
        life.mem_g_n = int(d["mem_g_n"])


def _mem_align(life, d):
    """One memory row per Connection, whether or not the state file carried it.

    The memory keeps one row per relation and a relation is a Connection, so the
    rows are made to the Connections' own length.  A state file written before
    this round kept its relations in a table of its own; what it does not carry
    starts empty rather than being invented, and the first moment that really
    continues one writes the real value over it.

    What the memory holds besides the rows is its own index -- which end each
    Connection stands on -- and that is derived here, once, the way the address
    space is.
    """
    n = len(life.cn_pre)
    n_state = len(life.bar_d)
    way = [float(v) for v in getattr(life, "cn_way", [])]
    if len(way) < n:
        way += [1.0] * (n - len(way))
    life.cn_way = way[:n]
    key = [[float(x) for x in row] for row in getattr(life, "cn_key", [])]
    if len(key) < n:
        key += [[0.0] * n_state for _ in range(n - len(key))]
    life.cn_key = key[:n]
    s_row = [float(v) for v in d.get("mem_s", [])]
    if len(s_row) < n:
        s_row += [0.0] * (n - len(s_row))
    life.mem_s = s_row[:n]
    hit_row = [int(v) for v in d.get("mem_hit", [])]
    if len(hit_row) < n:
        hit_row += [0] * (n - len(hit_row))
    life.mem_hit = hit_row[:n]
    lam0 = life.mem_lam
    life.mem_act = [x if x > 0.0 else lam0 for x in life.mem_s]
    life.mem_act_age = [life.age] * n
    life._mem_index_build()
    life._mem_front_seed()
    return n


def _tup(x):
    """Ends and edges come back as tuples, so an identity is a hashable key."""
    if isinstance(x, (list, tuple)):
        return tuple(_tup(v) for v in x)
    return x


def _split(key):
    a, b = key.split("|")
    return (int(a), int(b))


def _restore_history(life, d):
    """Put the history back, and let the current running form again."""
    if not d:
        return
    life.cn_pre = [int(v) for v in d.get("cn_pre", [])]
    life.cn_post = [int(v) for v in d.get("cn_post", [])]
    life.cn_born = [int(v) for v in d.get("cn_born", [])]
    life.cn_peak = [float(v) for v in d.get("cn_peak", [])]
    life.cn_live = [0.0] * len(life.cn_pre)
    life.cn_now = {}          # per pair, formed again as it is judged
    life.cn_form = [0.0] * len(life.cn_pre)
    life.cn_index = dict(((p, q), k) for k, (p, q)
                         in enumerate(zip(life.cn_pre, life.cn_post)))
    # what the memory keeps for each relation, off the history, and then made to
    # the Connections' own length and indexed by them
    life.cn_way = [float(v) for v in d.get("cn_way", [])]
    life.cn_key = [[float(x) for x in row] for row in d.get("cn_key", [])]
    _mem_align(life, d)
    life.el_ends = [_tup(t) for t in d.get("el_ends", [])]
    life.el_born = [int(v) for v in d.get("el_born", [])]
    life.el_frames = [int(v) for v in d.get("el_frames", [])]
    # the parts each identity has played are history and come back with it;
    # what it is acting as this moment, and what it is reading of its own
    # channels, are this run's own and start empty beside it (V3.0 2.9)
    life.el_sides = [set(int(s) for s in v) for v in d.get("el_sides", [])]
    life.el_now = []
    life.el_form = []
    life.el_index = {}
    for i, mem in enumerate(life.el_ends):
        life.el_index.setdefault(tuple(sorted(mem)), i)
    life._align_now()
    life.st_ids = [int(v) for v in d.get("st_ids", [])]
    life.st_ends = [_tup(t) for t in d.get("st_ends", [])]
    life.st_edges = [_tup(t) for t in d.get("st_edges", [])]
    life.st_born = [int(v) for v in d.get("st_born", [])]
    life.st_frames = Running(int(v) for v in d.get("st_frames", []))
    life.st_index = {}
    for i in range(len(life.st_ids)):
        life.st_index[(life.st_ends[i], life.st_edges[i])] = i
    life.rn_start = [int(v) for v in d.get("rn_start", [])]
    life.rn_stop = [None if v is None else int(v)
                    for v in d.get("rn_stop", [])]
    life.rn_struct = [int(v) for v in d.get("rn_struct", [])]
    life.sf_way = dict((int(k), int(v)) for k, v in (d.get("sf_way") or {}).items())
    life.sf_born_in = dict((int(k), int(v))
                           for k, v in (d.get("sf_born_in") or {}).items())
    life.sf_frames = dict((_split(k), int(v))
                          for k, v in (d.get("sf_frames") or {}).items())
    # the counts each connection has really been judged for
    life.sf_hist = dict((k, []) for k in life.sf_way)
    life.sf_live_hist = dict((k, []) for k in life.sf_way)
    life.sf_form_hist = dict((k, []) for k in life.sf_way)
    # the states, and the identity every place stands for: a Life read back is
    # the same Life, and its running layer has to find the same places it left
    life.sf_state = dict((int(k), int(v))
                         for k, v in (d.get("sf_state") or {}).items())
    life.sf_run = dict((int(k), int(v))
                       for k, v in (d.get("sf_run") or {}).items())
    for name in ("unit_kind", "unit_ref", "st_unit", "st_form", "st_run_open",
                 "rn_unit", "rn_form", "rn_on", "rn_brought", "rn_epi_open",
                 "rn_ord", "wd_order"):
        if name in d:
            setattr(life, name, list(d[name]))
    if "rn_by" in d:
        life.rn_by = [list(v) for v in d["rn_by"]]
    if "rn_epi" in d:
        life.rn_epi = [[[int(a), None if b is None else int(b)] for a, b in ep]
                       for ep in d["rn_epi"]]
    if "wd_unit" in d:
        life.wd_unit = dict((k, int(v)) for k, v in d["wd_unit"].items())
    if "wd_seen" in d:
        life.wd_seen = dict((k, int(v)) for k, v in d["wd_seen"].items())
    if "wd_born" in d:
        life.wd_born = dict((k, int(v)) for k, v in d["wd_born"].items())
    if life.unit_kind:
        # every place that came back already has its slot: nothing is given
        # twice, and the first moment after a read-back finds them where they
        # were left
        life.pr_st_done = len(life.st_ids)
        life.pr_all_done = len(life.rn_start)
        life.walk_ow_done = len(life.st_ids)
        life.pr_seeded = False
        life.walk_seeded = False


# ----------------------------------------------------------------------
# the state file: the manifest, and the values themselves beside it
#
# One file, and in it two parts.  The first is the manifest: the payload,
# exactly the payload the JSON file held, except that every run of floats long
# enough to be worth it is left out of the text and replaced by
#
#     {"#f64": [byte_offset, count, dims...]}
#
# saying where in the second part its values lie.  The second part is those
# values: little-endian float64, eight bytes each, as they are held.
#
# What this does not do: it does not round, average, merge or reorder anything.
# Every float comes back bit for bit, every integer, identity, table length and
# order keeps its place, and the number of relations is what it was.  Only the
# way the numbers are written down changes.
def _uniform_floats(node):
    """(flat values, dims) when this is a rectangle of floats, else None."""
    if type(node) is not list or not node:
        return None
    if all(type(x) is float for x in node):
        return node, (len(node),)
    if all(type(x) is list for x in node):
        rects = [_uniform_floats(x) for x in node]
        if any(r is None for r in rects):
            return None
        dims = rects[0][1]
        for r in rects:
            if r[1] != dims:
                return None
        flat = []
        for r in rects:
            flat.extend(r[0])
        return flat, (len(node),) + dims
    return None


def _state_manifest(payload, blocks):
    """The payload, with every worthwhile run of floats left to the blocks."""
    def enc(node):
        rect = _uniform_floats(node)
        if rect is not None and len(rect[0]) >= STATE_BLOCK_MIN:
            values, dims = rect
            off = len(blocks)
            a = array.array("d", values)
            if sys.byteorder != "little":
                a.byteswap()
            blocks.extend(a.tobytes())
            return {"#f64": [off, len(values)] + list(dims)}
        if type(node) is list:
            return [enc(x) for x in node]
        if type(node) is dict:
            if "#f64" in node:
                raise ValueError("a state field may not be named #f64")
            return dict((k, enc(v)) for k, v in node.items())
        return node
    return enc(payload)


def _state_block_to_list(a, dims):
    """One block's values, as nested lists, as the writer left them."""
    def go(start, dims):
        if len(dims) == 1:
            return list(a[start:start + dims[0]]), start + dims[0]
        rows = []
        pos = start
        for _ in range(dims[0]):
            row, pos = go(pos, dims[1:])
            rows.append(row)
        return rows, pos
    return go(0, dims)[0]


def _state_decode(manifest, blob):
    """The manifest and the blocks -> the payload they stand for."""
    def dec(node):
        if type(node) is dict:
            if len(node) == 1 and "#f64" in node:
                d = node["#f64"]
                off, n = int(d[0]), int(d[1])
                a = array.array("d")
                a.frombytes(blob[off:off + 8 * n])
                if sys.byteorder != "little":
                    a.byteswap()
                return _state_block_to_list(a, [int(x) for x in d[2:]])
            return dict((k, dec(v)) for k, v in node.items())
        if type(node) is list:
            return [dec(x) for x in node]
        return node
    return dec(json.loads(manifest))


def _state_is_blocks(path):
    with open(path, "rb") as f:
        return f.read(len(STATE_MAGIC)) == STATE_MAGIC


def _write_state(path, payload):
    """The one file: the mark, the manifest, the blocks."""
    blocks = bytearray()
    manifest = json.dumps(_state_manifest(payload, blocks),
                          ensure_ascii=False).encode("utf-8")
    with open(path, "wb") as f:
        f.write(STATE_MAGIC)
        f.write(struct.pack(">Q", len(manifest)))
        f.write(manifest)
        f.write(blocks)
    return path


def _read_state(path):
    """The one file, back as the payload it stands for."""
    with open(path, "rb") as f:
        head = f.read(len(STATE_MAGIC) + 8)
        if head[:len(STATE_MAGIC)] != STATE_MAGIC:
            raise ValueError("not a block state file: %s" % path)
        n = struct.unpack(">Q", head[len(STATE_MAGIC):])[0]
        manifest = f.read(n).decode("utf-8")
        blob = f.read()
    return _state_decode(manifest, blob)


def _read_state_payload(path):
    """Read a state file, whichever way it is written."""
    if _state_is_blocks(path):
        return _read_state(path)
    with io.open(path, "r", encoding="utf-8") as f:
        return json.load(f)


# The state file is read once per load, not once per layer.  The load chain
# passes through every layer that ever wrote the file, and each of them
# opened and parsed it again: on a Life with 52 798 relations that was the
# same file parsed over and over.  They all get this one reading.  Nothing
# writes to it.
_PAYLOAD_PATH = None
_PAYLOAD = None


def _read_payload(path):
    """The payload of the load that is running, read from the file once."""
    if _PAYLOAD is not None and _PAYLOAD_PATH == path:
        return _PAYLOAD
    return _read_state_payload(path)


def _trunk_sections(life, meta=None):
    """The trunk's own sections, in the order the trunk wrote them.

    Both writers take the payload from here, so the JSON file and the block
    file cannot drift apart.
    """
    life._end_align()
    return {
        "format": STATE_FORMAT,
        "dna": {k: v for k, v in vars(life._base_dna).items()},
        "life": {f: getattr(life, f) for f in LIFE_FIELDS_18},
        "trace": {f: getattr(life, f) for f in TRACE_FIELDS},
        "memory": {f: getattr(life, f) for f in MEMORY_FIELDS},
        "meta": meta or {},
    }


def dump_life(life, path, meta=None):
    """Write the Life, and the history it has formed, into one file.

    The trunk's sections are the sections it always wrote, in the order it
    wrote them; the organ's experience and the history are put beside them in
    their own sections, and the top-level `format` says so.  The file is
    written once, in the block state format.  Nothing is validated on the way
    in.

    `_trunk_dump` is the older writer, which wrote the same payload as JSON.
    It is kept so that a file of that shape can still be written and compared
    against; the formal path does not use it.
    """
    payload = _trunk_sections(life, meta=meta)
    payload[EXPRESSION_SECTION] = life.expression_memory()
    if getattr(life, "history_enabled", True):
        payload[HISTORY_SECTION] = _history_of(life)
    return _write_state(path, payload)


def load_life(path, inlet=None, **switches):
    """Read the Life back, and the history it had formed along with it.

    The history is taken out first and kept on its own, then the trunk loads
    exactly as it loaded, and the history is put back: identities and
    organisation come back, while what is acting on the very next moment and
    which of the three states anything is in are formed again from what really
    happens (V3.0 2.9).  Both ways of writing the file are read.

    The address space is built here, once.  It is derived and nothing else: it
    is the buckets the Connections fall into, so it is built where that memory
    is whole -- after the trunk has read the relation tables and the history has
    been put back -- and before the Life runs.  Every layer of the
    chain above rebuilds it for the Life it was about to hand on, and
    only the last of those rebuilds was ever kept: on 52 798 relations that was
    26 rebuilds of a table derived from the same rows, 25 of them thrown away,
    and they were the whole of a load's cost.  The build itself is unchanged --
    same planes, same buckets, same rule -- and so is every table it touches.
    """
    global _PAYLOAD_PATH, _PAYLOAD
    _PAYLOAD_PATH, _PAYLOAD = path, _read_state_payload(path)
    try:
        grown = _PAYLOAD.get(HISTORY_SECTION) or {}
        out, meta = _trunk_load(path, inlet, **switches)
    finally:
        _PAYLOAD_PATH, _PAYLOAD = None, None
    grown_now = bool(getattr(out, "history_enabled", True) and grown)
    if grown_now:
        _restore_history(out, grown)
        out._str_rebuild_index()
        out._end_align()
    out._addr_build()
    if grown_now:
        out._start_walks()
        out._walk_seed()
        out._pr_seed()
        out._carry_seed()
        # and the scales it had itself read, back in the places standing the
        # walks up has just put a fresh Life's defaults
        _own_scales_of(out, grown)
    return out, meta
