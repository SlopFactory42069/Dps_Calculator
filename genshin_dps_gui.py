#!/usr/bin/env python3
"""
Genshin Impact Team DPS Calculator – GUI Edition
================================================
Full graphical interface to create, edit, delete and persist:
  - Characters
  - Weapons
  - Artifacts / Artifact Sets
  - Buff templates
  - Rotations (hits + timed buffs)
  - Run DPS calculations with precise buff uptime

Data is saved to genshin_data.json next to this script.
"""

from __future__ import annotations

import json
import os
import tempfile
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, filedialog
from dataclasses import dataclass, field, asdict, is_dataclass
from typing import Dict, List, Optional, Any, Tuple, Callable
from enum import Enum, auto
from copy import deepcopy
import math
import uuid
from pathlib import Path


# =============================================================================
# CORE DATA MODEL (same logic as the CLI version, kept self-contained)
# =============================================================================

class Element(str, Enum):
    PHYSICAL = "Physical"
    PYRO = "Pyro"
    HYDRO = "Hydro"
    ELECTRO = "Electro"
    CRYO = "Cryo"
    ANEMO = "Anemo"
    GEO = "Geo"
    DENDRO = "Dendro"


class ReactionType(str, Enum):
    NONE = "None"
    # Amplifying (multiply the hit)
    VAPORIZE_HYDRO = "Vaporize (Hydro trigger ×2)"
    VAPORIZE_PYRO = "Vaporize (Pyro trigger ×1.5)"
    MELT_PYRO = "Melt (Pyro trigger ×2)"
    MELT_CRYO = "Melt (Cryo trigger ×1.5)"
    # Additive (add flat base to the hit)
    AGGRAVATE = "Aggravate"
    SPREAD = "Spread"
    # Classic transformative (Level + EM, no ATK/CRIT by default)
    OVERLOAD = "Overload"
    SUPERCONDUCT = "Superconduct"
    ELECTRO_CHARGED = "Electro-Charged"
    SWIRL = "Swirl"
    SHATTER = "Shatter"
    BLOOM = "Bloom"
    HYPERBLOOM = "Hyperbloom"
    BURGEON = "Burgeon"
    BURNING = "Burning"
    # Lunar reactions (can CRIT; shallower EM curve; damage element fixed or overrideable)
    LUNAR_CHARGED = "Lunar-Charged"
    LUNAR_BLOOM = "Lunar-Bloom"
    LUNAR_CRYSTALLIZE = "Lunar-Crystallize"
    # Stellar reactions (Direct versions scale with ATK/EM/CRIT; element can be Electro/Cryo/Anemo)
    STELLAR_CONDUCT = "Stellar-Conduct"
    STELLAR_SWIRL = "Stellar-Swirl"
    STELLAR_SWIRL_VORTEX_LV1 = "Stellar-Swirl (Vortex Lv1)"
    STELLAR_SWIRL_VORTEX_LV2 = "Stellar-Swirl (Vortex Lv2)"


# Default damage element for pure reaction instances.
# For multi-element reactions (Swirl, Stellar-Conduct) the hit's element_override / talent element is used.
REACTION_DAMAGE_ELEMENT = {
    "Overload": "Pyro",
    "Superconduct": "Cryo",
    "Electro-Charged": "Electro",
    "Swirl": None,              # uses hit element (absorbed)
    "Shatter": "Physical",
    "Bloom": "Dendro",
    "Hyperbloom": "Dendro",
    "Burgeon": "Dendro",
    "Burning": "Pyro",
    "Lunar-Charged": "Electro",
    "Lunar-Bloom": "Dendro",
    "Lunar-Crystallize": "Geo",
    "Stellar-Conduct": None,                   # Electro or Cryo – use hit element
    "Stellar-Swirl": None,                     # Anemo (initial) or Cryo – use hit element
    "Stellar-Swirl (Vortex Lv1)": "Cryo",
    "Stellar-Swirl (Vortex Lv2)": "Cryo",
}

# Classic transformative multipliers (post-5.2 values)
CLASSIC_TRANSFORMATIVE_MULT = {
    "Overload": 2.75,
    "Superconduct": 1.5,
    "Electro-Charged": 2.0,
    "Swirl": 0.6,
    "Shatter": 3.0,
    "Bloom": 2.0,
    "Hyperbloom": 3.0,
    "Burgeon": 3.0,
    "Burning": 0.25,
}

# Lunar / Stellar base reaction coefficients (KQM / community)
# Stellar-Swirl reaction: initial Anemo hit ×0.75; Vortex explosion Cryo ×2 (Lv1) or ×3 (Lv2).
# Stellar-Conduct Direct uses Polestar stacks (1.0–2.0); default mid-stack 1.5.
LUNAR_STELLAR_MULT = {
    "Lunar-Charged": 3.0,
    "Lunar-Bloom": 1.0,
    "Lunar-Crystallize": 1.6,
    "Stellar-Conduct": 1.5,
    "Stellar-Swirl": 0.75,                 # default = initial Anemo hit
    "Stellar-Swirl (Vortex Lv1)": 2.0,
    "Stellar-Swirl (Vortex Lv2)": 3.0,
}

CLASSIC_TRANSFORMATIVE = set(CLASSIC_TRANSFORMATIVE_MULT.keys())
LUNAR_STELLAR = set(LUNAR_STELLAR_MULT.keys())
ALL_PURE_REACTION = CLASSIC_TRANSFORMATIVE | LUNAR_STELLAR

# Reactions whose pure (non-Direct) instances blend up to 4 contributors
# with weights 1 + 1/2 + 1/12 + 1/12 after ranking by personal expected damage.
MULTI_CONTRIBUTOR_REACTIONS = {
    "Lunar-Charged",
    "Lunar-Crystallize",
    "Stellar-Swirl",
    "Stellar-Swirl (Vortex Lv1)",
    "Stellar-Swirl (Vortex Lv2)",
}
MULTI_CONTRIBUTOR_WEIGHTS = [1.0, 0.5, 1.0 / 12.0, 1.0 / 12.0]


def blend_contributor_damages(personals: List[float]) -> float:
    """Rank personal damages high→low and apply 1 + ½ + 1/12 + 1/12.
    Missing contributors are dropped (weights are not renormalised)."""
    if not personals:
        return 0.0
    ranked = sorted(personals, reverse=True)
    total = 0.0
    for i, dmg in enumerate(ranked[:4]):
        total += dmg * MULTI_CONTRIBUTOR_WEIGHTS[i]
    return total


class TalentType(str, Enum):
    """Damage source / talent category – many buffs only apply to specific types."""
    NORMAL = "Normal Attack"
    CHARGED = "Charged Attack"
    PLUNGE = "Plunging Attack"
    SKILL = "Elemental Skill"
    BURST = "Elemental Burst"
    OTHER = "Other"


LEVEL_MULTIPLIER_90 = 1446.85
DATA_FILE = Path(__file__).parent / "genshin_data.json"
TALENT_TYPES = [t.value for t in TalentType]

# KQM Standard (KQMS) average 5★ substat roll values
# Source: https://compendium.keqingmains.com/  — 40 total rolls:
#   20 fixed (2 of every substat type) + 20 distributed optimally.
KQM_ROLL = {
    "hp_pct": 0.0496,
    "flat_hp": 253.94,
    "atk_pct": 0.0496,
    "flat_atk": 16.54,
    "def_pct": 0.0620,
    "flat_def": 19.68,
    "em": 19.82,
    "crit_rate": 0.0331,
    "crit_dmg": 0.0662,
    "er": 0.0551,
}
# 5★ main stats at +20
MAIN_STATS_20 = {
    "flat_hp": 4780.0,       # Flower
    "flat_atk": 311.0,       # Plume
    "atk_pct": 0.466,
    "hp_pct": 0.466,
    "def_pct": 0.583,
    "em": 187.0,
    "er": 0.518,
    "elem_dmg": 0.466,       # Goblet elemental
    "physical_dmg": 0.583,
    "crit_rate": 0.311,
    "crit_dmg": 0.622,
    "healing": 0.359,
}


def enum_to_str(obj):
    if isinstance(obj, Enum):
        return obj.value
    return obj


def build_kqm_stats(
    sands: str = "atk_pct",
    goblet: str = "elem_dmg",
    circlet: str = "crit_rate",
    element: str = "Pyro",
    extra_useful_rolls: int = 0,
    useful_priority: Optional[List[str]] = None,
) -> Tuple[Stats, Stats]:
    """
    Build (main_stats, sub_stats) following KQM Standard.
    - Fixed: 2 rolls of every substat type
    - Distributed: 20 rolls into useful stats (default CRIT Rate / CRIT DMG / ATK%)
    - extra_useful_rolls: additional distributed rolls on top of the 20 (KQM+N)
    Returns main Stats and sub Stats separately (for Artifact storage).
    """
    if useful_priority is None:
        useful_priority = ["crit_rate", "crit_dmg", "atk_pct"]

    main = Stats()
    # Flower + Plume fixed
    main.flat_hp += MAIN_STATS_20["flat_hp"]
    main.flat_atk += MAIN_STATS_20["flat_atk"]
    # Sands
    if sands == "atk_pct":
        main.atk_pct += MAIN_STATS_20["atk_pct"]
    elif sands == "hp_pct":
        main.hp_pct += MAIN_STATS_20["hp_pct"]
    elif sands == "def_pct":
        main.def_pct += MAIN_STATS_20["def_pct"]
    elif sands == "em":
        main.em += MAIN_STATS_20["em"]
    elif sands == "er":
        main.er += MAIN_STATS_20["er"]
    # Goblet
    if goblet == "elem_dmg":
        main.dmg_bonus[element] = main.dmg_bonus.get(element, 0.0) + MAIN_STATS_20["elem_dmg"]
    elif goblet == "physical_dmg":
        main.dmg_bonus["Physical"] = main.dmg_bonus.get("Physical", 0.0) + MAIN_STATS_20["physical_dmg"]
    elif goblet == "atk_pct":
        main.atk_pct += MAIN_STATS_20["atk_pct"]
    elif goblet == "hp_pct":
        main.hp_pct += MAIN_STATS_20["hp_pct"]
    elif goblet == "em":
        main.em += MAIN_STATS_20["em"]
    # Circlet
    if circlet == "crit_rate":
        main.crit_rate += MAIN_STATS_20["crit_rate"]
    elif circlet == "crit_dmg":
        main.crit_dmg += MAIN_STATS_20["crit_dmg"]
    elif circlet == "atk_pct":
        main.atk_pct += MAIN_STATS_20["atk_pct"]
    elif circlet == "hp_pct":
        main.hp_pct += MAIN_STATS_20["hp_pct"]
    elif circlet == "healing":
        pass  # not tracked as damage stat
    elif circlet == "em":
        main.em += MAIN_STATS_20["em"]

    # Subs: 2 fixed of each + 20 distributed (+ extra)
    sub = Stats()
    fixed = 2
    sub.hp_pct += KQM_ROLL["hp_pct"] * fixed
    sub.flat_hp += KQM_ROLL["flat_hp"] * fixed
    sub.atk_pct += KQM_ROLL["atk_pct"] * fixed
    sub.flat_atk += KQM_ROLL["flat_atk"] * fixed
    sub.def_pct += KQM_ROLL["def_pct"] * fixed
    sub.flat_def += KQM_ROLL["flat_def"] * fixed
    sub.em += KQM_ROLL["em"] * fixed
    sub.crit_rate += KQM_ROLL["crit_rate"] * fixed
    sub.crit_dmg += KQM_ROLL["crit_dmg"] * fixed
    sub.er += KQM_ROLL["er"] * fixed

    distributed = 20 + max(0, extra_useful_rolls)
    # Split distributed rolls across useful_priority (favor first stats slightly)
    # Simple even-ish split with remainder to first stats
    n = len(useful_priority)
    base_each = distributed // n
    remainder = distributed % n
    for i, key in enumerate(useful_priority):
        rolls = base_each + (1 if i < remainder else 0)
        val = KQM_ROLL.get(key, 0.0) * rolls
        if key == "crit_rate":
            sub.crit_rate += val
        elif key == "crit_dmg":
            sub.crit_dmg += val
        elif key == "atk_pct":
            sub.atk_pct += val
        elif key == "hp_pct":
            sub.hp_pct += val
        elif key == "def_pct":
            sub.def_pct += val
        elif key == "em":
            sub.em += val
        elif key == "er":
            sub.er += val
        elif key == "flat_atk":
            sub.flat_atk += val
        elif key == "flat_hp":
            sub.flat_hp += val

    return main, sub


@dataclass
class Stats:
    base_atk: float = 0.0
    atk_pct: float = 0.0
    flat_atk: float = 0.0
    base_hp: float = 0.0
    hp_pct: float = 0.0
    flat_hp: float = 0.0
    base_def: float = 0.0
    def_pct: float = 0.0
    flat_def: float = 0.0
    em: float = 0.0
    er: float = 0.0
    crit_rate: float = 0.05
    crit_dmg: float = 0.50
    dmg_bonus: Dict[str, float] = field(default_factory=dict)  # element name -> value
    all_dmg_bonus: float = 0.0
    reaction_bonus: Dict[str, float] = field(default_factory=dict)
    def_reduction: float = 0.0
    def_ignore: float = 0.0
    res_shred: Dict[str, float] = field(default_factory=dict)

    def total_atk(self) -> float:
        return (self.base_atk * (1.0 + self.atk_pct)) + self.flat_atk

    def total_hp(self) -> float:
        return (self.base_hp * (1.0 + self.hp_pct)) + self.flat_hp

    def total_def(self) -> float:
        return (self.base_def * (1.0 + self.def_pct)) + self.flat_def

    def get_dmg_bonus(self, element: str) -> float:
        return self.dmg_bonus.get(element, 0.0) + self.all_dmg_bonus

    def copy(self) -> "Stats":
        return deepcopy(self)

    def apply(self, other: "Stats") -> "Stats":
        r = self.copy()
        r.base_atk += other.base_atk
        r.atk_pct += other.atk_pct
        r.flat_atk += other.flat_atk
        r.base_hp += other.base_hp
        r.hp_pct += other.hp_pct
        r.flat_hp += other.flat_hp
        r.base_def += other.base_def
        r.def_pct += other.def_pct
        r.flat_def += other.flat_def
        r.em += other.em
        r.er += other.er
        r.crit_rate += other.crit_rate
        r.crit_dmg += other.crit_dmg
        r.all_dmg_bonus += other.all_dmg_bonus
        r.def_reduction = min(0.9, r.def_reduction + other.def_reduction)
        r.def_ignore += other.def_ignore
        for k, v in other.dmg_bonus.items():
            r.dmg_bonus[k] = r.dmg_bonus.get(k, 0.0) + v
        for k, v in other.res_shred.items():
            r.res_shred[k] = r.res_shred.get(k, 0.0) + v
        for k, v in other.reaction_bonus.items():
            r.reaction_bonus[k] = r.reaction_bonus.get(k, 0.0) + v
        return r

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "Stats":
        if d is None:
            return cls()
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


@dataclass
class Weapon:
    name: str
    base_atk: float = 0.0
    substat_type: str = "atk_pct"      # which field the substat goes into
    substat_value: float = 0.0
    passive: Stats = field(default_factory=Stats)
    notes: str = ""

    def get_stats(self) -> Stats:
        s = Stats(base_atk=self.base_atk)
        if self.substat_type and hasattr(s, self.substat_type):
            setattr(s, self.substat_type, getattr(s, self.substat_type) + self.substat_value)
        elif self.substat_type.endswith("_dmg"):
            el = self.substat_type.replace("_dmg", "").capitalize()
            s.dmg_bonus[el] = s.dmg_bonus.get(el, 0.0) + self.substat_value
        return s.apply(self.passive)

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "base_atk": self.base_atk,
            "substat_type": self.substat_type,
            "substat_value": self.substat_value,
            "passive": self.passive.to_dict(),
            "notes": self.notes,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Weapon":
        return cls(
            name=d["name"],
            base_atk=d.get("base_atk", 0.0),
            substat_type=d.get("substat_type", "atk_pct"),
            substat_value=d.get("substat_value", 0.0),
            passive=Stats.from_dict(d.get("passive")),
            notes=d.get("notes", ""),
        )


@dataclass
class Artifact:
    name: str                          # e.g. "Xiangling Emblem set"
    main_stats: Stats = field(default_factory=Stats)
    sub_stats: Stats = field(default_factory=Stats)
    set_2pc: Stats = field(default_factory=Stats)
    set_4pc: Stats = field(default_factory=Stats)
    notes: str = ""

    def get_stats(self) -> Stats:
        return self.main_stats.apply(self.sub_stats).apply(self.set_2pc).apply(self.set_4pc)

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "main_stats": self.main_stats.to_dict(),
            "sub_stats": self.sub_stats.to_dict(),
            "set_2pc": self.set_2pc.to_dict(),
            "set_4pc": self.set_4pc.to_dict(),
            "notes": self.notes,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Artifact":
        return cls(
            name=d["name"],
            main_stats=Stats.from_dict(d.get("main_stats")),
            sub_stats=Stats.from_dict(d.get("sub_stats")),
            set_2pc=Stats.from_dict(d.get("set_2pc")),
            set_4pc=Stats.from_dict(d.get("set_4pc")),
            notes=d.get("notes", ""),
        )


@dataclass
class TalentHit:
    """One named damage instance on a character (N1, Skill hit 2, Burst tick, Guoba, …)."""
    name: str
    multiplier: float
    talent_type: str = "Normal Attack"   # Normal / Charged / Plunge / Skill / Burst / Other
    element: str = "Physical"
    scaling_stat: str = "atk"            # atk / hp / def / em
    # If True, this talent snapshots: use buffs from snapshot_time (cast time), not each tick time.
    # Classic examples: Xiangling Pyronado, Fischl Oz (partial), Beidou Q, etc.
    snapshots: bool = False

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "TalentHit":
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


@dataclass
class ComboHit:
    """One step inside a combo: which talent, when relative to combo start."""
    talent_name: str
    time_offset: float                   # seconds after combo start
    reaction: str = "None"
    count: int = 1
    # If set, snapshot_time = combo_start + this offset (for snapshotted talents inside the combo)
    snapshot_offset: Optional[float] = None

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "ComboHit":
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


@dataclass
class Combo:
    """
    Named sequence of talents with relative timings.
    Example Skirk-style N5D: N1@0, N2@0.3, … N5@1.2, special@1.5, N1@2.0, …
    Insert into a rotation at time T → expands to absolute hits at T + offset.
    """
    name: str
    hits: List[ComboHit] = field(default_factory=list)
    notes: str = ""

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "hits": [h.to_dict() for h in self.hits],
            "notes": self.notes,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Combo":
        return cls(
            name=d["name"],
            hits=[ComboHit.from_dict(h) for h in d.get("hits", [])],
            notes=d.get("notes", ""),
        )


@dataclass
class Character:
    name: str
    element: str = "Pyro"
    level: int = 90
    base_stats: Stats = field(default_factory=Stats)   # character base only
    weapon_name: str = ""
    artifact_name: str = ""
    # Free-form list of named hits – add as many as you want
    talents: List[TalentHit] = field(default_factory=list)
    # Named combos: sequences of talents with relative timings
    combos: List[Combo] = field(default_factory=list)
    constellation: int = 0
    notes: str = ""

    def get_talent(self, name: str) -> Optional["TalentHit"]:
        for t in self.talents:
            if t.name == name:
                return t
        return None

    def talent_names(self) -> List[str]:
        return [t.name for t in self.talents]

    def get_combo(self, name: str) -> Optional[Combo]:
        for c in self.combos:
            if c.name == name:
                return c
        return None

    def combo_names(self) -> List[str]:
        return [c.name for c in self.combos]

    def expand_combo(self, combo_name: str, start_time: float) -> List["Hit"]:
        """Turn a combo into absolute-time Hits for a rotation."""
        combo = self.get_combo(combo_name)
        if not combo:
            return []
        result = []
        for ch in combo.hits:
            snap = None
            if ch.snapshot_offset is not None:
                snap = start_time + ch.snapshot_offset
            result.append(Hit(
                time=start_time + ch.time_offset,
                character=self.name,
                talent_name=ch.talent_name,
                reaction=ch.reaction,
                count=ch.count,
                snapshot_time=snap,
            ))
        return result

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "element": self.element,
            "level": self.level,
            "base_stats": self.base_stats.to_dict(),
            "weapon_name": self.weapon_name,
            "artifact_name": self.artifact_name,
            "talents": [t.to_dict() for t in self.talents],
            "combos": [c.to_dict() for c in self.combos],
            "constellation": self.constellation,
            "notes": self.notes,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Character":
        talents: List[TalentHit] = []
        if d.get("talents"):
            talents = [TalentHit.from_dict(t) for t in d["talents"]]
        else:
            def add_list(values, prefix, ttype, element):
                if not values:
                    return
                if isinstance(values, (int, float)):
                    values = [values]
                for i, m in enumerate(values, 1):
                    label = f"{prefix}{i}" if len(values) > 1 else prefix
                    talents.append(TalentHit(name=label, multiplier=float(m),
                                             talent_type=ttype, element=element))
            el = d.get("element", "Pyro")
            add_list(d.get("normal", []), "N", TalentType.NORMAL.value, el)
            charged = d.get("charged", [])
            if isinstance(charged, (int, float)):
                charged = [charged] if charged else []
            add_list(charged, "Charged", TalentType.CHARGED.value, el)
            add_list(d.get("plunge", []), "Plunge", TalentType.PLUNGE.value, el)
            add_list(d.get("skill", []), "Skill", TalentType.SKILL.value, el)
            add_list(d.get("burst", []), "Burst", TalentType.BURST.value, el)
            for name, m in d.get("custom_talents", {}).items():
                talents.append(TalentHit(name=name, multiplier=float(m),
                                         talent_type=TalentType.OTHER.value, element=el))

        combos = [Combo.from_dict(c) for c in d.get("combos", [])]

        return cls(
            name=d.get("name", "Unnamed"),
            element=d.get("element", "Pyro"),
            level=d.get("level", 90),
            base_stats=Stats.from_dict(d.get("base_stats")),
            weapon_name=d.get("weapon_name", ""),
            artifact_name=d.get("artifact_name", ""),
            talents=talents,
            combos=combos,
            constellation=d.get("constellation", 0),
            notes=d.get("notes", ""),
        )


# What a provider-scaled buff can read from the buffer character.
# IMPORTANT: these always use the provider's PERMANENT stats only
# (character base + weapon + artifacts). Temporary team buffs are NEVER included,
# which prevents infinite mutual-buff loops (e.g. two characters buffing each
# other's ATK based on current ATK).
PROVIDER_STAT_CHOICES = [
    "none",           # fixed stats only (default)
    "base_atk",       # white ATK only (char + weapon) — Bennett style
    "personal_atk",   # permanent total ATK (base * (1+atk%) + flat from artifacts)
    "personal_hp",
    "personal_def",
    "personal_em",
]


@dataclass
class BuffTemplate:
    name: str
    stats: Stats = field(default_factory=Stats)  # fixed part of the buff
    default_duration: float = 10.0
    # If empty → applies to all talent types. Otherwise only listed types receive the buff.
    talent_types: List[str] = field(default_factory=list)
    notes: str = ""

    # --- Provider-scaled portion (optional) ---
    # If provider_name is set and provider_stat != "none", the calculator reads that
    # character's permanent stats (no temporary buffs) and adds:
    #   target_field += provider_stat_value * provider_multiplier
    provider_name: str = ""              # character who grants the scaled value
    provider_stat: str = "none"          # one of PROVIDER_STAT_CHOICES
    provider_multiplier: float = 1.0     # e.g. 1.0 for Bennett C1 talent 12-ish
    # Which field on the *receiver* gets the scaled value
    # Common: "flat_atk" (Bennett/Sara), or we use additive flat on hits for quills
    provider_target: str = "flat_atk"    # flat_atk | flat_hp | flat_def | em | additive_base

    def applies_to(self, talent_type: str) -> bool:
        if not self.talent_types:
            return True
        return talent_type in self.talent_types

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "stats": self.stats.to_dict(),
            "default_duration": self.default_duration,
            "talent_types": self.talent_types,
            "notes": self.notes,
            "provider_name": self.provider_name,
            "provider_stat": self.provider_stat,
            "provider_multiplier": self.provider_multiplier,
            "provider_target": self.provider_target,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "BuffTemplate":
        return cls(
            name=d["name"],
            stats=Stats.from_dict(d.get("stats")),
            default_duration=d.get("default_duration", 10.0),
            talent_types=d.get("talent_types", []),
            notes=d.get("notes", ""),
            provider_name=d.get("provider_name", ""),
            provider_stat=d.get("provider_stat", "none"),
            provider_multiplier=d.get("provider_multiplier", 1.0),
            provider_target=d.get("provider_target", "flat_atk"),
        )


@dataclass
class Hit:
    """
    A damage instance in a rotation.
    Primary lookup: character + talent_name → pulls multiplier, type, element, scaling from the character.
    Optional overrides still available for reaction / count / additive / transformative.

    Snapshotting:
      If the talent has snapshots=True, set snapshot_time to the cast time (e.g. when XL burst was pressed).
      Buffs active at snapshot_time are locked for this hit even if they have expired by hit.time.
      If snapshot_time is None but talent.snapshots is True, the calculator will warn and fall back to hit.time.
    """
    time: float
    character: str
    talent_name: str                     # must match a TalentHit.name on the character
    reaction: str = "None"
    additive_base: float = 0.0
    is_transformative: bool = False
    count: int = 1
    # Snapshot lock time (seconds). None = dynamic (use buffs at hit.time)
    snapshot_time: Optional[float] = None
    # Optional overrides (leave empty/None to use the talent definition)
    name_override: str = ""              # display name; defaults to talent_name
    multiplier_override: Optional[float] = None
    element_override: str = ""
    talent_type_override: str = ""
    scaling_override: str = ""
    # Up to 3 extra characters who also contributed to a multi-contributor
    # reaction (Lunar-Charged, Lunar-Crystallize, Stellar-Swirl). Used only
    # for pure reaction instances; ranked and blended 1 + 1/2 + 1/12 + 1/12.
    extra_contributors: List[str] = field(default_factory=list)
    # When hits come from Insert Combo, they share a combo_group id so the
    # rotation tree can nest them under one parent and delete the whole group.
    combo_group: Optional[str] = None
    combo_label: str = ""  # display name of the source combo, e.g. "N5D"

    @property
    def display_name(self) -> str:
        return self.name_override or self.talent_name

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "Hit":
        d = dict(d)
        # Migrate old format that stored name/multiplier/element/talent_type directly
        if "talent_name" not in d and "name" in d:
            d["talent_name"] = d.pop("name", "Hit")
            d.setdefault("name_override", d.get("talent_name", ""))
        for old_key, new_key in [
            ("multiplier", "multiplier_override"),
            ("element", "element_override"),
            ("talent_type", "talent_type_override"),
            ("scaling_stat", "scaling_override"),
        ]:
            if old_key in d and new_key not in d:
                d[new_key] = d.pop(old_key)
        # Drop unknown keys
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


@dataclass
class TimedBuff:
    template_name: str
    start: float
    duration: float
    # optional override of stats if needed later
    notes: str = ""

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "TimedBuff":
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


@dataclass
class Rotation:
    name: str
    duration: float = 20.0
    hits: List[Hit] = field(default_factory=list)
    timed_buffs: List[TimedBuff] = field(default_factory=list)
    notes: str = ""

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "duration": self.duration,
            "hits": [h.to_dict() for h in self.hits],
            "timed_buffs": [b.to_dict() for b in self.timed_buffs],
            "notes": self.notes,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Rotation":
        return cls(
            name=d["name"],
            duration=d.get("duration", 20.0),
            hits=[Hit.from_dict(h) for h in d.get("hits", [])],
            timed_buffs=[TimedBuff.from_dict(b) for b in d.get("timed_buffs", [])],
            notes=d.get("notes", ""),
        )


@dataclass
class Enemy:
    level: int = 90
    res: Dict[str, float] = field(default_factory=lambda: {
        "Physical": 0.10, "Pyro": 0.10, "Hydro": 0.10, "Electro": 0.10,
        "Cryo": 0.10, "Anemo": 0.10, "Geo": 0.10, "Dendro": 0.10,
    })

    def to_dict(self) -> dict:
        return {"level": self.level, "res": self.res}

    @classmethod
    def from_dict(cls, d: dict) -> "Enemy":
        if not isinstance(d, dict):
            raise ValueError("enemy entry must be an object")
        res = cls().res
        loaded = d.get("res", {})
        if not isinstance(loaded, dict):
            raise ValueError("enemy 'res' must be an object")
        res.update({str(k): float(v) for k, v in loaded.items()})
        return cls(level=int(d.get("level", 90)), res=res)


# =============================================================================
# DAMAGE FORMULAS
# =============================================================================

def resistance_multiplier(res: float) -> float:
    if res < 0:
        return 1.0 - (res / 2.0)
    elif res < 0.75:
        return 1.0 - res
    return 1.0 / (1.0 + 4.0 * res)


def defense_multiplier(char_level: int, enemy_level: int,
                       def_reduction: float = 0.0, def_ignore: float = 0.0) -> float:
    def_reduction = min(0.9, def_reduction)
    char = char_level + 100
    enemy = (enemy_level + 100) * (1.0 - def_reduction) * (1.0 - def_ignore)
    return char / (char + enemy)


def amplifying_multiplier(reaction: str, em: float, reaction_bonus: float = 0.0) -> float:
    base_map = {
        "Vaporize (Hydro trigger ×2)": 2.0,
        "Melt (Pyro trigger ×2)": 2.0,
        "Vaporize (Pyro trigger ×1.5)": 1.5,
        "Melt (Cryo trigger ×1.5)": 1.5,
    }
    base = base_map.get(reaction, 1.0)
    if base == 1.0:
        return 1.0
    em_bonus = 2.78 * em / (1400.0 + em) if em > 0 else 0.0
    return base * (1.0 + em_bonus + reaction_bonus)


def additive_reaction_bonus(reaction: str, em: float, reaction_bonus: float = 0.0) -> float:
    if reaction == "Aggravate":
        mult = 1.15
    elif reaction == "Spread":
        mult = 1.25
    else:
        return 0.0
    em_bonus = 5.0 * em / (1200.0 + em) if em > 0 else 0.0
    return mult * LEVEL_MULTIPLIER_90 * (1.0 + em_bonus + reaction_bonus)


def _reaction_bonus_key(reaction: str) -> str:
    """Normalize reaction name for looking up reaction_bonus in Stats."""
    r = reaction.lower()
    for key in ("vaporize", "melt", "overload", "superconduct", "electro-charged",
                "swirl", "shatter", "bloom", "hyperbloom", "burgeon", "burning",
                "aggravate", "spread", "lunar-charged", "lunar-bloom",
                "lunar-crystallize", "stellar-conduct", "stellar-swirl"):
        if key in r:
            # Vortex variants still use stellar-swirl reaction bonus
            if "stellar-swirl" in r:
                return "stellar-swirl"
            return key
    return r.split()[0] if r else ""


def classic_transformative_damage(reaction: str, em: float, res_mult: float,
                                  reaction_bonus: float = 0.0) -> float:
    """Classic transformative: LevelMult × ReactionMult × (1 + 16·EM/(2000+EM) + bonus) × RES.
    Cannot CRIT (unless special passives like Nahida C2, handled externally)."""
    base_mult = CLASSIC_TRANSFORMATIVE_MULT.get(reaction, 0.0)
    if base_mult == 0.0:
        return 0.0
    em_bonus = 16.0 * em / (2000.0 + em) if em > 0 else 0.0
    return base_mult * LEVEL_MULTIPLIER_90 * (1.0 + em_bonus + reaction_bonus) * res_mult


def lunar_stellar_damage(
    reaction: str,
    em: float,
    res_mult: float,
    reaction_bonus: float = 0.0,
    *,
    # For Direct Lunar/Stellar that also scale with talent:
    use_talent_base: bool = False,
    talent_base: float = 0.0,
    dmg_bonus: float = 1.0,
    def_mult: float = 1.0,
    can_crit: bool = True,
    crit_rate: float = 0.0,
    crit_dmg: float = 0.5,
) -> Tuple[float, float, float]:
    """
    Lunar & Stellar reaction damage.
    - Shallower EM curve: 6·EM/(2000+EM) (approx community value).
    - Can CRIT using the character's CRIT stats (or fixed Transformative CRIT from passives).
    - Direct versions can optionally fold in a talent base (ATK × MV etc.).
    Returns (non_crit, average, crit).
    """
    base_mult = LUNAR_STELLAR_MULT.get(reaction, 0.0)
    if base_mult == 0.0:
        return 0.0, 0.0, 0.0

    # Shallower EM curve used by Lunar / Stellar family
    em_bonus = 6.0 * em / (2000.0 + em) if em > 0 else 0.0

    if use_talent_base and talent_base > 0:
        # Direct Lunar/Stellar (from character kits):
        #   talent_base × reaction_coeff × (1 + EM_bonus + reaction_bonus) × RES × CRIT
        # Ignores enemy DEF. Normal Elemental DMG% usually does NOT apply
        # (only Lunar/Stellar-specific reaction bonuses do — already in reaction_bonus).
        raw = talent_base * base_mult * (1.0 + em_bonus + reaction_bonus) * res_mult
    else:
        # Pure reaction instance (thundercloud tick, Vortex explosion, etc.)
        # LevelMult × coeff × (1 + EM + bonus) × RES × CRIT — ignores DEF
        raw = base_mult * LEVEL_MULTIPLIER_90 * (1.0 + em_bonus + reaction_bonus) * res_mult

    if not can_crit:
        return raw, raw, raw
    cr = min(1.0, max(0.0, crit_rate))
    cd = crit_dmg
    return raw, raw * (1.0 + cr * cd), raw * (1.0 + cd)


def reaction_damage_element(reaction: str, hit_element: str) -> str:
    """Resolve which elemental RES / DMG Bonus the reaction instance uses."""
    fixed = REACTION_DAMAGE_ELEMENT.get(reaction)
    if fixed is not None:
        return fixed
    # Swirl / Stellar-Conduct / Stellar-Swirl: use the element of the hit
    return hit_element or "Physical"


def calculate_hit_damage(
    *,
    multiplier: float,
    element: str,
    scaling_stat: str,
    reaction: str,
    additive_base: float,
    is_transformative: bool,
    count: int,
    stats: Stats,
    char_level: int,
    enemy: Enemy,
) -> Tuple[float, float, float]:
    """Returns (non_crit, average, crit)."""
    r_key = _reaction_bonus_key(reaction)
    r_bonus = stats.reaction_bonus.get(r_key, 0.0)

    # ----- Pure reaction damage (classic transformative or Lunar/Stellar) -----
    is_pure = is_transformative or reaction in ALL_PURE_REACTION
    if is_pure:
        dmg_element = reaction_damage_element(reaction, element)
        res = enemy.res.get(dmg_element, 0.10) - stats.res_shred.get(dmg_element, 0.0)
        res_mult = resistance_multiplier(res)

        if reaction in CLASSIC_TRANSFORMATIVE:
            dmg = classic_transformative_damage(reaction, stats.em, res_mult, r_bonus) * count
            return dmg, dmg, dmg

        if reaction in LUNAR_STELLAR:
            # Pure Lunar/Stellar instance (e.g. thundercloud tick)
            non, avg, crit = lunar_stellar_damage(
                reaction, stats.em, res_mult, r_bonus,
                can_crit=True,
                crit_rate=stats.crit_rate,
                crit_dmg=stats.crit_dmg,
            )
            return non * count, avg * count, crit * count

    # ----- Normal talent hit (optionally amplified / additive / Direct Lunar-Stellar) -----
    if scaling_stat == "atk":
        scale = stats.total_atk()
    elif scaling_stat == "hp":
        scale = stats.total_hp()
    elif scaling_stat == "def":
        scale = stats.total_def()
    elif scaling_stat == "em":
        scale = stats.em
    else:
        scale = stats.total_atk()

    base_dmg = scale * multiplier + additive_base

    if reaction in ("Aggravate", "Spread"):
        base_dmg += additive_reaction_bonus(reaction, stats.em, r_bonus)

    dmg_bonus = 1.0 + stats.get_dmg_bonus(element)
    cr = min(1.0, max(0.0, stats.crit_rate))
    cd = stats.crit_dmg
    def_mult = defense_multiplier(char_level, enemy.level, stats.def_reduction, stats.def_ignore)
    res = enemy.res.get(element, 0.10) - stats.res_shred.get(element, 0.0)
    res_mult = resistance_multiplier(res)

    # Direct Lunar / Stellar damage dealt by a talent (kit-dealt reaction DMG)
    # Scales with talent base × reaction coeff × EM curve × RES × CRIT; ignores DEF
    # and normal Elemental DMG%. Element for RES is the reaction's damage element.
    if reaction in LUNAR_STELLAR and not is_transformative:
        dmg_element = reaction_damage_element(reaction, element)
        res = enemy.res.get(dmg_element, 0.10) - stats.res_shred.get(dmg_element, 0.0)
        res_mult = resistance_multiplier(res)
        non, avg, crit = lunar_stellar_damage(
            reaction, stats.em, res_mult, r_bonus,
            use_talent_base=True,
            talent_base=base_dmg,
            can_crit=True,
            crit_rate=cr,
            crit_dmg=cd,
        )
        return non * count, avg * count, crit * count

    # Amplifying reactions
    amp = amplifying_multiplier(reaction, stats.em, r_bonus)

    common = base_dmg * dmg_bonus * def_mult * res_mult * amp * count
    return common, common * (1.0 + cr * cd), common * (1.0 + cd)


# =============================================================================
# DATA STORE
# =============================================================================

class DataStore:
    def __init__(self):
        self.weapons: Dict[str, Weapon] = {}
        self.artifacts: Dict[str, Artifact] = {}
        self.characters: Dict[str, Character] = {}
        self.buff_templates: Dict[str, BuffTemplate] = {}
        self.rotations: Dict[str, Rotation] = {}
        self.enemy = Enemy()
        self.path: Path = DATA_FILE
        self.load()

    def load(self, path: Optional[Path] = None) -> bool:
        """Load a save file. All-or-nothing: if anything in the file is invalid,
        the current data is left completely untouched and False is returned.
        On success the loaded file becomes the active save location."""
        path = Path(path) if path else self.path
        if not path.exists():
            return False
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                raise ValueError("top level of the file must be a JSON object")

            def parse_section(key, factory):
                section = data.get(key, {})
                if not isinstance(section, dict):
                    raise ValueError(f"section '{key}' must be an object")
                out = {}
                for name, entry in section.items():
                    try:
                        out[name] = factory(entry)
                    except Exception as e:
                        raise ValueError(f"{key} entry '{name}' is invalid: {e!r}") from e
                return out

            # Build everything into temporaries first...
            weapons = parse_section("weapons", Weapon.from_dict)
            artifacts = parse_section("artifacts", Artifact.from_dict)
            characters = parse_section("characters", Character.from_dict)
            buff_templates = parse_section("buff_templates", BuffTemplate.from_dict)
            rotations = parse_section("rotations", Rotation.from_dict)
            try:
                enemy = Enemy.from_dict(data["enemy"]) if "enemy" in data else Enemy()
            except Exception as e:
                raise ValueError(f"enemy settings are invalid: {e!r}") from e
        except Exception as e:
            messagebox.showerror("Load Error", f"Failed to load '{path}':\n{e}\n\nYour current data was not changed.")
            return False

        # ...then commit in one go, replacing (not merging with) the old data.
        self.weapons = weapons
        self.artifacts = artifacts
        self.characters = characters
        self.buff_templates = buff_templates
        self.rotations = rotations
        self.enemy = enemy
        self.path = path
        return True

    def save(self, path: Optional[Path] = None) -> bool:
        """Atomically write the data. Writes to a temp file in the same folder,
        flushes it to disk, then swaps it over the target with os.replace, so an
        interrupted save can never leave a half-written file. A successful save
        makes `path` the active save location."""
        target = Path(path) if path else self.path
        data = {
            "weapons": {k: v.to_dict() for k, v in self.weapons.items()},
            "artifacts": {k: v.to_dict() for k, v in self.artifacts.items()},
            "characters": {k: v.to_dict() for k, v in self.characters.items()},
            "buff_templates": {k: v.to_dict() for k, v in self.buff_templates.items()},
            "rotations": {k: v.to_dict() for k, v in self.rotations.items()},
            "enemy": self.enemy.to_dict(),
        }
        tmp_name = None
        try:
            payload = json.dumps(data, indent=2)  # serialize first: fail before touching disk
            fd, tmp_name = tempfile.mkstemp(dir=str(target.parent),
                                            prefix=target.name + ".", suffix=".tmp")
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                f.write(payload)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp_name, target)
            tmp_name = None
            try:  # persist the rename itself (POSIX only; harmless to skip elsewhere)
                dfd = os.open(str(target.parent), os.O_RDONLY)
                try:
                    os.fsync(dfd)
                finally:
                    os.close(dfd)
            except (OSError, AttributeError):
                pass
            self.path = target
            return True
        except Exception as e:
            messagebox.showerror("Save Error", f"Failed to save data:\n{e}")
            return False
        finally:
            if tmp_name and os.path.exists(tmp_name):
                try:
                    os.remove(tmp_name)
                except OSError:
                    pass

    def get_character_full_stats(self, char_name: str) -> Stats:
        """Permanent stats only: character base + weapon + artifacts. NO temporary buffs."""
        char = self.characters[char_name]
        s = char.base_stats.copy()
        if char.weapon_name and char.weapon_name in self.weapons:
            s = s.apply(self.weapons[char.weapon_name].get_stats())
        if char.artifact_name and char.artifact_name in self.artifacts:
            s = s.apply(self.artifacts[char.artifact_name].get_stats())
        return s

    def get_provider_stat_value(self, char_name: str, stat_key: str) -> float:
        """
        Read a provider's permanent stat for scaling a buff.
        Never includes temporary team buffs — this is the anti-loop rule.
        """
        if not char_name or char_name not in self.characters or stat_key == "none":
            return 0.0
        s = self.get_character_full_stats(char_name)
        if stat_key == "base_atk":
            # White ATK only (character base_atk field already holds char base;
            # weapon adds more base_atk via get_stats)
            return s.base_atk
        if stat_key == "personal_atk":
            return s.total_atk()
        if stat_key == "personal_hp":
            return s.total_hp()
        if stat_key == "personal_def":
            return s.total_def()
        if stat_key == "personal_em":
            return s.em
        return 0.0

    def resolve_buff_template(self, tmpl: "BuffTemplate") -> Tuple[Stats, float]:
        """
        Build the actual Stats this buff grants, plus optional additive_base
        (for quill-style flat damage that is not ATK but additive base DMG).

        Returns (stats_for_receiver, additive_base_bonus).
        """
        stats = tmpl.stats.copy()
        additive = 0.0
        if tmpl.provider_stat and tmpl.provider_stat != "none" and tmpl.provider_name:
            value = self.get_provider_stat_value(tmpl.provider_name, tmpl.provider_stat)
            scaled = value * tmpl.provider_multiplier
            target = tmpl.provider_target or "flat_atk"
            if target == "additive_base":
                additive += scaled
            elif target == "flat_atk":
                stats.flat_atk += scaled
            elif target == "flat_hp":
                stats.flat_hp += scaled
            elif target == "flat_def":
                stats.flat_def += scaled
            elif target == "em":
                stats.em += scaled
            elif target == "atk_pct":
                stats.atk_pct += scaled
            elif target == "hp_pct":
                stats.hp_pct += scaled
            elif target == "def_pct":
                stats.def_pct += scaled
        return stats, additive


# =============================================================================
# UNDO / REDO
# =============================================================================

class UndoManager:
    """Simple action-stack undo/redo. Each entry is (undo_callable, redo_callable)."""

    def __init__(self, max_depth: int = 80):
        self._undo: List[Tuple[Callable[[], None], Callable[[], None], str]] = []
        self._redo: List[Tuple[Callable[[], None], Callable[[], None], str]] = []
        self.max_depth = max_depth

    def push(self, undo_fn: Callable[[], None], redo_fn: Callable[[], None], label: str = ""):
        self._undo.append((undo_fn, redo_fn, label))
        if len(self._undo) > self.max_depth:
            self._undo.pop(0)
        self._redo.clear()

    def can_undo(self) -> bool:
        return bool(self._undo)

    def can_redo(self) -> bool:
        return bool(self._redo)

    def undo_label(self) -> str:
        return self._undo[-1][2] if self._undo else ""

    def redo_label(self) -> str:
        return self._redo[-1][2] if self._redo else ""

    def undo(self) -> Optional[str]:
        if not self._undo:
            return None
        undo_fn, redo_fn, label = self._undo.pop()
        undo_fn()
        self._redo.append((undo_fn, redo_fn, label))
        return label

    def redo(self) -> Optional[str]:
        if not self._redo:
            return None
        undo_fn, redo_fn, label = self._redo.pop()
        redo_fn()
        self._undo.append((undo_fn, redo_fn, label))
        return label

    def clear(self):
        self._undo.clear()
        self._redo.clear()


def bind_combobox_refresh(cb: ttk.Combobox, values_fn: Callable[[], List[str]]):
    """Refresh a Combobox's value list every time the user opens it."""
    def _refresh(_event=None):
        try:
            current = cb.get()
            vals = values_fn()
            cb["values"] = vals
            # Preserve selection if still valid
            if current and current in vals:
                cb.set(current)
        except tk.TclError:
            pass
    cb.bind("<ButtonPress-1>", _refresh, add="+")
    cb.bind("<Down>", _refresh, add="+")
    cb.bind("<space>", _refresh, add="+")


# =============================================================================
# GUI HELPERS
# =============================================================================

class StatsEditor(ttk.LabelFrame):
    """Reusable form for editing a Stats object."""

    FIELDS = [
        ("base_atk", "Base ATK"),
        ("atk_pct", "ATK %"),
        ("flat_atk", "Flat ATK"),
        ("base_hp", "Base HP"),
        ("hp_pct", "HP %"),
        ("flat_hp", "Flat HP"),
        ("base_def", "Base DEF"),
        ("def_pct", "DEF %"),
        ("flat_def", "Flat DEF"),
        ("em", "Elemental Mastery"),
        ("er", "Energy Recharge"),
        ("crit_rate", "CRIT Rate"),
        ("crit_dmg", "CRIT DMG"),
        ("all_dmg_bonus", "All DMG %"),
        ("def_reduction", "DEF Reduction"),
        ("def_ignore", "DEF Ignore"),
    ]

    def __init__(self, parent, title="Stats", **kwargs):
        super().__init__(parent, text=title, **kwargs)
        self.vars: Dict[str, tk.StringVar] = {}
        row = 0
        for key, label in self.FIELDS:
            ttk.Label(self, text=label).grid(row=row, column=0, sticky="w", padx=4, pady=2)
            var = tk.StringVar(value="0")
            ent = ttk.Entry(self, textvariable=var, width=12)
            ent.grid(row=row, column=1, sticky="w", padx=4, pady=2)
            self.vars[key] = var
            row += 1

        # Elemental DMG bonuses (compact)
        ttk.Label(self, text="Elemental DMG %").grid(row=row, column=0, sticky="w", padx=4, pady=2)
        self.dmg_frame = ttk.Frame(self)
        self.dmg_frame.grid(row=row, column=1, sticky="w")
        self.dmg_vars: Dict[str, tk.StringVar] = {}
        for i, el in enumerate(["Pyro", "Hydro", "Electro", "Cryo", "Anemo", "Geo", "Dendro", "Physical"]):
            ttk.Label(self.dmg_frame, text=el[:3]).grid(row=0, column=i*2, padx=1)
            v = tk.StringVar(value="0")
            ttk.Entry(self.dmg_frame, textvariable=v, width=5).grid(row=0, column=i*2+1, padx=1)
            self.dmg_vars[el] = v
        row += 1

        # RES shred
        ttk.Label(self, text="RES Shred").grid(row=row, column=0, sticky="w", padx=4, pady=2)
        self.res_frame = ttk.Frame(self)
        self.res_frame.grid(row=row, column=1, sticky="w")
        self.res_vars: Dict[str, tk.StringVar] = {}
        for i, el in enumerate(["Pyro", "Hydro", "Electro", "Cryo", "Anemo", "Geo", "Dendro", "Physical"]):
            ttk.Label(self.res_frame, text=el[:3]).grid(row=0, column=i*2, padx=1)
            v = tk.StringVar(value="0")
            ttk.Entry(self.res_frame, textvariable=v, width=5).grid(row=0, column=i*2+1, padx=1)
            self.res_vars[el] = v

    def load(self, stats: Stats):
        for key, var in self.vars.items():
            val = getattr(stats, key, 0.0)
            var.set(f"{val:.4g}" if isinstance(val, float) else str(val))
        for el, var in self.dmg_vars.items():
            var.set(f"{stats.dmg_bonus.get(el, 0.0):.4g}")
        for el, var in self.res_vars.items():
            var.set(f"{stats.res_shred.get(el, 0.0):.4g}")

    def get(self) -> Stats:
        def f(key):
            try:
                return float(self.vars[key].get() or 0)
            except ValueError:
                return 0.0
        s = Stats(
            base_atk=f("base_atk"), atk_pct=f("atk_pct"), flat_atk=f("flat_atk"),
            base_hp=f("base_hp"), hp_pct=f("hp_pct"), flat_hp=f("flat_hp"),
            base_def=f("base_def"), def_pct=f("def_pct"), flat_def=f("flat_def"),
            em=f("em"), er=f("er"),
            crit_rate=f("crit_rate"), crit_dmg=f("crit_dmg"),
            all_dmg_bonus=f("all_dmg_bonus"),
            def_reduction=f("def_reduction"), def_ignore=f("def_ignore"),
        )
        for el, var in self.dmg_vars.items():
            try:
                v = float(var.get() or 0)
                if v:
                    s.dmg_bonus[el] = v
            except ValueError:
                pass
        for el, var in self.res_vars.items():
            try:
                v = float(var.get() or 0)
                if v:
                    s.res_shred[el] = v
            except ValueError:
                pass
        return s


def _wheel_delta(event) -> int:
    """Normalize mouse-wheel delta across platforms (positive = scroll up)."""
    if getattr(event, "num", None) == 4:  # Linux scroll up
        return 1
    if getattr(event, "num", None) == 5:  # Linux scroll down
        return -1
    delta = getattr(event, "delta", 0) or 0
    # Windows: multiples of 120; macOS: small integers
    if abs(delta) >= 120:
        return 1 if delta > 0 else -1
    return 1 if delta > 0 else -1


def bind_mousewheel(widget, target=None):
    """
    Bind mouse-wheel scrolling to `widget` so that hovering and scrolling
    moves `target` (defaults to widget itself). Works for Canvas, Listbox,
    Text, and ttk.Treeview on Windows / macOS / Linux.
    """
    target = target or widget

    def _on_wheel(event):
        steps = _wheel_delta(event)
        try:
            if isinstance(target, tk.Canvas):
                target.yview_scroll(-steps * 3, "units")
            elif isinstance(target, (tk.Listbox, tk.Text)):
                target.yview_scroll(-steps * 3, "units")
            else:
                # Treeview and other ttk widgets
                target.yview_scroll(-steps * 3, "units")
        except tk.TclError:
            pass
        return "break"

    # Windows / macOS
    widget.bind("<MouseWheel>", _on_wheel, add="+")
    # Linux
    widget.bind("<Button-4>", _on_wheel, add="+")
    widget.bind("<Button-5>", _on_wheel, add="+")
    # Also bind when pointer is over children of a canvas-scrolled frame
    for child_bind in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
        try:
            widget.bind_all  # noqa: just ensure attr exists
        except Exception:
            pass


def make_scrollable(parent, bg: Optional[str] = None) -> Tuple[ttk.Frame, ttk.Frame, tk.Canvas]:
    """Return (container, inner_frame, canvas) where inner_frame is scrollable."""
    container = ttk.Frame(parent)
    canvas = tk.Canvas(container, highlightthickness=0, borderwidth=0)
    if bg:
        canvas.configure(bg=bg)
    scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
    inner = ttk.Frame(canvas)
    inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

    window_id = canvas.create_window((0, 0), window=inner, anchor="nw")

    def _stretch_inner(event):
        # Keep inner frame at least as wide as the canvas
        canvas.itemconfigure(window_id, width=event.width)

    canvas.bind("<Configure>", _stretch_inner)
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")
    bind_mousewheel(canvas, canvas)
    bind_mousewheel(inner, canvas)

    def _bind_child_wheel(_event=None):
        def _walk(w):
            bind_mousewheel(w, canvas)
            try:
                for ch in w.winfo_children():
                    _walk(ch)
            except tk.TclError:
                pass
        _walk(inner)

    inner.bind("<Map>", lambda e: inner.after(80, _bind_child_wheel), add="+")
    container._rebind_wheel = _bind_child_wheel  # type: ignore[attr-defined]
    return container, inner, canvas


def enable_mousewheel_on_descendants(root_widget, scroll_targets=None):
    """Recursively bind mouse-wheel so scrollable widgets respond under the pointer."""

    def _bind_tree(w):
        if isinstance(w, (tk.Listbox, tk.Text, tk.Canvas, ttk.Treeview)):
            bind_mousewheel(w)
        try:
            for child in w.winfo_children():
                _bind_tree(child)
        except tk.TclError:
            pass

    _bind_tree(root_widget)


# =============================================================================
# MAIN APPLICATION
# =============================================================================

class GenshinDPSApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Genshin Impact Team DPS Calculator")
        self.geometry("1200x800")
        self.minsize(980, 640)

        self.store = DataStore()
        self.undo_mgr = UndoManager()

        self._apply_theme()

        # Menu
        menubar = tk.Menu(self)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Save", command=self.save_data, accelerator="Ctrl+S")
        file_menu.add_command(label="Save As…", command=self.save_as)
        file_menu.add_command(label="Load…", command=self.load_from)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        edit_menu = tk.Menu(menubar, tearoff=0)
        edit_menu.add_command(label="Undo", command=self.do_undo, accelerator="Ctrl+Z")
        edit_menu.add_command(label="Redo", command=self.do_redo, accelerator="Ctrl+Y")
        menubar.add_cascade(label="Edit", menu=edit_menu)
        self.config(menu=menubar)

        self.bind("<Control-s>", lambda e: self.save_data())
        self.bind("<Control-z>", lambda e: self.do_undo())
        self.bind("<Control-y>", lambda e: self.do_redo())
        self.bind("<Control-Z>", lambda e: self.do_undo())
        self.bind("<Control-Y>", lambda e: self.do_redo())

        # Notebook
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=8, pady=(8, 4))

        self._build_characters_tab()
        self._build_weapons_tab()
        self._build_artifacts_tab()
        self._build_buffs_tab()
        self._build_rotations_tab()
        self._build_calculator_tab()
        self._build_enemy_tab()

        # Status bar
        status_frame = ttk.Frame(self)
        status_frame.pack(fill="x", side="bottom", padx=4, pady=2)
        self.status = tk.StringVar(value="Ready – data auto-loads from genshin_data.json")
        ttk.Label(status_frame, textvariable=self.status, relief="sunken", anchor="w",
                  padding=(6, 3)).pack(fill="x")

        self.refresh_all_lists()
        self._wire_combobox_refreshes()
        self._style_tk_widgets()
        enable_mousewheel_on_descendants(self)
        # Re-bind wheel on scrollable tab contents after widgets finish mapping
        self.after(200, self._rebind_all_scroll_wheels)
        self._update_title()

    def _rebind_all_scroll_wheels(self):
        enable_mousewheel_on_descendants(self)
        for name in ("_char_canvas", "_wpn_canvas", "_art_canvas", "_buff_canvas", "_rot_canvas"):
            # canvases themselves already bound; also walk their parent containers
            pass
        # Walk every widget that exposed _rebind_wheel
        def _walk(w):
            rebind = getattr(w, "_rebind_wheel", None)
            if callable(rebind):
                try:
                    rebind()
                except Exception:
                    pass
            try:
                for ch in w.winfo_children():
                    _walk(ch)
            except tk.TclError:
                pass
        _walk(self)

    def _style_tk_widgets(self):
        """Apply dark colors to classic tk widgets (Listbox / Text / Canvas)."""
        c = self.colors
        for w in (
            getattr(self, "char_listbox", None),
            getattr(self, "weapon_listbox", None),
            getattr(self, "art_listbox", None),
            getattr(self, "buff_listbox", None),
            getattr(self, "rot_listbox", None),
            getattr(self, "char_combo_list", None),
        ):
            if w is None:
                continue
            w.configure(
                bg=c["tree_bg"], fg=c["fg"],
                selectbackground=c["select"], selectforeground="#ffffff",
                highlightthickness=0, borderwidth=1,
                relief="solid",
                font=("Segoe UI", 9),
            )
            bind_mousewheel(w)
        if hasattr(self, "calc_text"):
            self.calc_text.configure(
                bg=c["tree_bg"], fg=c["fg"],
                insertbackground=c["fg"],
                selectbackground=c["select"], selectforeground="#ffffff",
                highlightthickness=0,
            )
            bind_mousewheel(self.calc_text)
        for tree in (getattr(self, "hits_tree", None), getattr(self, "tbuff_tree", None),
                     getattr(self, "char_talent_tree", None), getattr(self, "combo_hits_tree", None)):
            if tree is not None:
                bind_mousewheel(tree)

    def _apply_theme(self):
        """Dark-mode visual theme via ttk styles + shared color tokens."""
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        # Dark palette
        self.colors = {
            "bg": "#1e1e2e",
            "bg2": "#2a2a3d",
            "bg3": "#33334a",
            "fg": "#e4e4ef",
            "fg_dim": "#9a9ab0",
            "accent": "#7aa2f7",
            "accent2": "#bb9af7",
            "select": "#3d5a80",
            "entry_bg": "#2b2b40",
            "border": "#3f3f5a",
            "tree_bg": "#252538",
            "danger": "#f7768e",
            "ok": "#9ece6a",
        }
        c = self.colors
        bg, fg = c["bg"], c["fg"]

        self.configure(bg=bg)
        style.configure(".", background=bg, foreground=fg, font=("Segoe UI", 9),
                        fieldbackground=c["entry_bg"], bordercolor=c["border"],
                        troughcolor=c["bg2"], darkcolor=c["bg2"], lightcolor=c["bg3"])
        style.configure("TFrame", background=bg)
        style.configure("TLabel", background=bg, foreground=fg, font=("Segoe UI", 9))
        style.configure("TLabelframe", background=bg, foreground=fg,
                        bordercolor=c["border"], font=("Segoe UI", 9, "bold"))
        style.configure("TLabelframe.Label", background=bg, foreground=c["accent"],
                        font=("Segoe UI", 9, "bold"))
        style.configure("TButton", font=("Segoe UI", 9), padding=(8, 4),
                        background=c["bg3"], foreground=fg, bordercolor=c["border"])
        style.map("TButton",
                  background=[("active", c["select"]), ("pressed", c["accent"])],
                  foreground=[("active", fg), ("pressed", "#ffffff")])
        style.configure("Accent.TButton", font=("Segoe UI", 9, "bold"), padding=(10, 5),
                        background=c["accent"], foreground="#0d1117")
        style.map("Accent.TButton",
                  background=[("active", c["accent2"]), ("pressed", c["select"])],
                  foreground=[("active", "#0d1117")])
        style.configure("Danger.TButton", font=("Segoe UI", 9), padding=(8, 4),
                        background=c["bg3"], foreground=c["danger"])
        style.configure("TNotebook", background=bg, borderwidth=0)
        style.configure("TNotebook.Tab", font=("Segoe UI", 9, "bold"), padding=(12, 6),
                        background=c["bg2"], foreground=c["fg_dim"])
        style.map("TNotebook.Tab",
                  background=[("selected", c["bg3"]), ("!selected", c["bg2"])],
                  foreground=[("selected", c["accent"]), ("!selected", c["fg_dim"])])
        style.configure("Treeview", font=("Consolas", 9), rowheight=24,
                        background=c["tree_bg"], fieldbackground=c["tree_bg"],
                        foreground=fg, bordercolor=c["border"])
        style.configure("Treeview.Heading", font=("Segoe UI", 9, "bold"),
                        background=c["bg3"], foreground=c["accent"])
        style.map("Treeview",
                  background=[("selected", c["select"])],
                  foreground=[("selected", "#ffffff")])
        style.configure("TEntry", padding=3, fieldbackground=c["entry_bg"],
                        foreground=fg, insertcolor=fg)
        style.configure("TCombobox", padding=3, fieldbackground=c["entry_bg"],
                        foreground=fg, background=c["bg3"])
        style.map("TCombobox",
                  fieldbackground=[("readonly", c["entry_bg"])],
                  foreground=[("readonly", fg)],
                  background=[("readonly", c["bg3"])])
        style.configure("TCheckbutton", background=bg, foreground=fg)
        style.map("TCheckbutton",
                  background=[("active", bg)],
                  foreground=[("active", fg)])
        style.configure("TScrollbar", background=c["bg3"], troughcolor=c["bg2"],
                        bordercolor=c["border"], arrowcolor=fg)
        style.configure("Header.TLabel", font=("Segoe UI", 11, "bold"),
                        foreground=c["accent"], background=bg)
        style.configure("Hint.TLabel", foreground=c["fg_dim"], background=bg,
                        font=("Segoe UI", 8))
        style.configure("TSeparator", background=c["border"])

        # Default option colors for tk widgets created later
        self.option_add("*Background", bg)
        self.option_add("*Foreground", fg)
        self.option_add("*selectBackground", c["select"])
        self.option_add("*selectForeground", "#ffffff")
        self.option_add("*Entry.Background", c["entry_bg"])
        self.option_add("*Entry.Foreground", fg)
        self.option_add("*Listbox.Background", c["tree_bg"])
        self.option_add("*Listbox.Foreground", fg)
        self.option_add("*Text.Background", c["tree_bg"])
        self.option_add("*Text.Foreground", fg)
        self.option_add("*Text.insertBackground", fg)
        self.option_add("*Canvas.Background", bg)

    # ----- Undo / Redo -----
    def do_undo(self):
        label = self.undo_mgr.undo()
        if label is None:
            self.status.set("Nothing to undo")
            return
        self.status.set(f"Undo: {label}")

    def do_redo(self):
        label = self.undo_mgr.redo()
        if label is None:
            self.status.set("Nothing to redo")
            return
        self.status.set(f"Redo: {label}")

    def _push_hits_undo(self, label: str):
        """Snapshot current rotation hits/tbuffs for undo around a mutation."""
        before_hits = deepcopy(self._current_hits)
        before_tbuffs = deepcopy(self._current_tbuffs)
        # After the mutation, the redo state is the new lists; we capture after via closure on call.
        def make_restore(hits, tbuffs):
            def restore():
                self._current_hits = deepcopy(hits)
                self._current_tbuffs = deepcopy(tbuffs)
                self._reload_hits_tree()
                self._reload_tbuffs_tree()
            return restore
        # Caller must call _commit_hits_undo after mutating
        self._pending_hits_undo = (before_hits, before_tbuffs, label, make_restore)

    def _commit_hits_undo(self):
        if not hasattr(self, "_pending_hits_undo") or self._pending_hits_undo is None:
            return
        before_hits, before_tbuffs, label, make_restore = self._pending_hits_undo
        self._pending_hits_undo = None
        after_hits = deepcopy(self._current_hits)
        after_tbuffs = deepcopy(self._current_tbuffs)
        self.undo_mgr.push(
            make_restore(before_hits, before_tbuffs),
            make_restore(after_hits, after_tbuffs),
            label,
        )

    def _push_store_dict_undo(self, dict_attr: str, key: str, old_val, new_val, label: str,
                              on_change: Optional[Callable] = None):
        """Undo for store.weapons/characters/etc dict set or delete (new_val None = delete)."""
        def undo():
            d = getattr(self.store, dict_attr)
            if old_val is None:
                d.pop(key, None)
            else:
                d[key] = deepcopy(old_val)
            if on_change:
                on_change()
        def redo():
            d = getattr(self.store, dict_attr)
            if new_val is None:
                d.pop(key, None)
            else:
                d[key] = deepcopy(new_val)
            if on_change:
                on_change()
        self.undo_mgr.push(undo, redo, label)

    # ----- Persistence -----
    def _update_title(self):
        self.title(f"Genshin Impact Team DPS Calculator – {self.store.path.name}")

    def save_data(self):
        if self.store.save():
            self._update_title()
            self.status.set(f"Saved to {self.store.path}")
            messagebox.showinfo("Saved", f"Data saved to:\n{self.store.path}")

    def save_as(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json")],
            initialdir=str(self.store.path.parent),
            initialfile=self.store.path.name,
        )
        if path and self.store.save(Path(path)):
            self._update_title()
            self.status.set(f"Saved to {path} (now the active save file)")

    def load_from(self):
        path = filedialog.askopenfilename(
            filetypes=[("JSON", "*.json")],
            initialdir=str(self.store.path.parent),
        )
        if path and self.store.load(Path(path)):
            self.undo_mgr.clear()
            self.reset_editors()
            self.refresh_all_lists()
            self.refresh_enemy_fields()
            self._update_title()
            self.status.set(f"Loaded from {path}")

    def reset_editors(self):
        """Clear every editor so nothing from the previous data stays on screen."""
        self.new_character()
        self.new_weapon()
        self.new_artifact()
        self.new_buff()
        self.new_rotation()
        self.calc_rotation.set("")
        self.calc_text.delete("1.0", tk.END)

    def refresh_enemy_fields(self):
        self.enemy_level.set(str(self.store.enemy.level))
        for el, var in self.enemy_res_vars.items():
            var.set(str(self.store.enemy.res.get(el, 0.10)))

    def refresh_all_lists(self):
        self.refresh_char_list()
        self.refresh_weapon_list()
        self.refresh_artifact_list()
        self.refresh_buff_list()
        self.refresh_rotation_list()
        self.refresh_calc_selectors()

    def _wire_combobox_refreshes(self):
        """Make every important dropdown re-query live data when opened."""
        # Characters tab
        bind_combobox_refresh(self.char_weapon_cb,
                              lambda: [""] + sorted(self.store.weapons.keys()))
        bind_combobox_refresh(self.char_artifact_cb,
                              lambda: [""] + sorted(self.store.artifacts.keys()))
        bind_combobox_refresh(self.ch_talent_cb,
                              lambda: [t.name for t in self._char_talents])
        # Buffs tab
        bind_combobox_refresh(self.buff_provider_cb,
                              lambda: [""] + sorted(self.store.characters.keys()))
        # Rotations tab
        bind_combobox_refresh(self.hit_char_cb,
                              lambda: sorted(self.store.characters.keys()))
        bind_combobox_refresh(self.hit_talent_cb, self._hit_talent_values)
        bind_combobox_refresh(self.ins_combo_char_cb,
                              lambda: sorted(self.store.characters.keys()))
        bind_combobox_refresh(self.ins_combo_cb, self._ins_combo_values)
        bind_combobox_refresh(self.tb_template_cb,
                              lambda: sorted(self.store.buff_templates.keys()))
        bind_combobox_refresh(self.hit_contrib1_cb,
                              lambda: [""] + sorted(self.store.characters.keys()))
        bind_combobox_refresh(self.hit_contrib2_cb,
                              lambda: [""] + sorted(self.store.characters.keys()))
        bind_combobox_refresh(self.hit_contrib3_cb,
                              lambda: [""] + sorted(self.store.characters.keys()))
        # Calculator
        bind_combobox_refresh(self.calc_rot_cb,
                              lambda: sorted(self.store.rotations.keys()))

    def _hit_talent_values(self) -> List[str]:
        cname = self.hit_char.get()
        if cname not in self.store.characters:
            return []
        return self.store.characters[cname].talent_names()

    def _ins_combo_values(self) -> List[str]:
        cname = self.ins_combo_char.get()
        if cname not in self.store.characters:
            return []
        return self.store.characters[cname].combo_names()

    # =========================================================================
    # CHARACTERS TAB
    # =========================================================================
    def _build_characters_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Characters")

        left = ttk.Frame(tab)
        left.pack(side="left", fill="y", padx=6, pady=6)
        ttk.Label(left, text="Characters", font=("", 11, "bold")).pack(anchor="w")
        self.char_listbox = tk.Listbox(left, width=28, height=25, exportselection=False)
        self.char_listbox.pack(fill="y", expand=True)
        self.char_listbox.bind("<<ListboxSelect>>", self.on_char_select)

        btn_frame = ttk.Frame(left)
        btn_frame.pack(fill="x", pady=4)
        ttk.Button(btn_frame, text="New", command=self.new_character).pack(side="left", padx=2)
        ttk.Button(btn_frame, text="Delete", command=self.delete_character).pack(side="left", padx=2)

        # Right – editor
        right_container, right, _char_canvas = make_scrollable(tab, bg=self.colors["bg"])
        right_container.pack(side="left", fill="both", expand=True, padx=6, pady=6)

        form = ttk.LabelFrame(right, text="Character Details")
        form.pack(fill="x", pady=4)

        self.char_name = tk.StringVar()
        self.char_element = tk.StringVar(value="Pyro")
        self.char_level = tk.StringVar(value="90")
        self.char_weapon = tk.StringVar()
        self.char_artifact = tk.StringVar()
        self.char_const = tk.StringVar(value="0")
        self.char_notes = tk.StringVar()

        r = 0
        for label, var in [
            ("Name", self.char_name),
            ("Element", self.char_element),
            ("Level", self.char_level),
            ("Constellation", self.char_const),
        ]:
            ttk.Label(form, text=label).grid(row=r, column=0, sticky="w", padx=4, pady=2)
            if label == "Element":
                ttk.Combobox(form, textvariable=var, values=[e.value for e in Element],
                             state="readonly", width=18).grid(row=r, column=1, sticky="w", padx=4)
            else:
                ttk.Entry(form, textvariable=var, width=22).grid(row=r, column=1, sticky="w", padx=4)
            r += 1

        ttk.Label(form, text="Weapon").grid(row=r, column=0, sticky="w", padx=4, pady=2)
        self.char_weapon_cb = ttk.Combobox(form, textvariable=self.char_weapon, width=20)
        self.char_weapon_cb.grid(row=r, column=1, sticky="w", padx=4)
        r += 1

        ttk.Label(form, text="Artifact Set").grid(row=r, column=0, sticky="w", padx=4, pady=2)
        self.char_artifact_cb = ttk.Combobox(form, textvariable=self.char_artifact, width=20)
        self.char_artifact_cb.grid(row=r, column=1, sticky="w", padx=4)
        r += 1

        ttk.Label(form, text="Notes").grid(row=r, column=0, sticky="w", padx=4, pady=2)
        ttk.Entry(form, textvariable=self.char_notes, width=40).grid(row=r, column=1, sticky="w", padx=4)

        # Base stats
        self.char_stats_editor = StatsEditor(right, title="Base Stats (character only, no weapon/artifacts)")
        self.char_stats_editor.pack(fill="x", pady=6)

        # Talents – free-form list of named hits
        tal = ttk.LabelFrame(right, text="Talents / Hits  (name · mult · type · element · scaling · snapshot)")
        tal.pack(fill="both", expand=True, pady=4)

        cols = ("name", "mult", "type", "element", "scaling", "snap")
        self.char_talent_tree = ttk.Treeview(tal, columns=cols, show="headings", height=8)
        for c, w, h in zip(cols, (110, 65, 110, 80, 65, 55),
                           ("Name", "Multiplier", "Type", "Element", "Scaling", "Snap?")):
            self.char_talent_tree.heading(c, text=h)
            self.char_talent_tree.column(c, width=w, anchor="center")
        self.char_talent_tree.pack(fill="both", expand=True, padx=4, pady=2)
        self.char_talent_tree.bind("<<TreeviewSelect>>", self.on_char_talent_select)

        # Editor row
        edit = ttk.Frame(tal)
        edit.pack(fill="x", padx=4, pady=4)
        self.ct_name = tk.StringVar()
        self.ct_mult = tk.StringVar(value="1.0")
        self.ct_type = tk.StringVar(value="Normal Attack")
        self.ct_element = tk.StringVar(value="Pyro")
        self.ct_scaling = tk.StringVar(value="atk")
        self.ct_snapshots = tk.BooleanVar(value=False)

        ttk.Label(edit, text="Name").grid(row=0, column=0, padx=2)
        ttk.Entry(edit, textvariable=self.ct_name, width=14).grid(row=0, column=1, padx=2)
        ttk.Label(edit, text="Mult").grid(row=0, column=2, padx=2)
        ttk.Entry(edit, textvariable=self.ct_mult, width=8).grid(row=0, column=3, padx=2)
        ttk.Label(edit, text="Type").grid(row=0, column=4, padx=2)
        ttk.Combobox(edit, textvariable=self.ct_type, values=TALENT_TYPES,
                     width=14, state="readonly").grid(row=0, column=5, padx=2)
        ttk.Label(edit, text="Element").grid(row=1, column=0, padx=2, pady=2)
        ttk.Combobox(edit, textvariable=self.ct_element, values=[e.value for e in Element],
                     width=12, state="readonly").grid(row=1, column=1, padx=2)
        ttk.Label(edit, text="Scaling").grid(row=1, column=2, padx=2)
        ttk.Combobox(edit, textvariable=self.ct_scaling, values=["atk", "hp", "def", "em"],
                     width=6, state="readonly").grid(row=1, column=3, padx=2)
        ttk.Checkbutton(edit, text="Snapshots (e.g. Pyronado)", variable=self.ct_snapshots).grid(
            row=1, column=4, columnspan=2, sticky="w", padx=4)

        btns = ttk.Frame(tal)
        btns.pack(fill="x", padx=4, pady=2)
        ttk.Button(btns, text="Add / Update Talent", command=self.add_char_talent).pack(side="left", padx=2)
        ttk.Button(btns, text="Remove Talent", command=self.remove_char_talent).pack(side="left", padx=2)

        self._char_talents: List[TalentHit] = []

        # ── Combos ──────────────────────────────────────────────────────────
        # Named sequences of talents with relative timings (e.g. Skirk N5D)
        combo_frame = ttk.LabelFrame(right, text="Combos  (named talent sequences with relative timings)")
        combo_frame.pack(fill="both", expand=True, pady=6)

        combo_top = ttk.Frame(combo_frame)
        combo_top.pack(fill="x", padx=4, pady=2)

        # Left: list of combos
        cl = ttk.Frame(combo_top)
        cl.pack(side="left", fill="y")
        ttk.Label(cl, text="Combos").pack(anchor="w")
        self.char_combo_list = tk.Listbox(cl, width=22, height=6, exportselection=False)
        self.char_combo_list.pack()
        self.char_combo_list.bind("<<ListboxSelect>>", self.on_char_combo_select)
        cbf = ttk.Frame(cl)
        cbf.pack(fill="x", pady=2)
        ttk.Button(cbf, text="New Combo", command=self.new_char_combo).pack(side="left", padx=1)
        ttk.Button(cbf, text="Delete", command=self.delete_char_combo).pack(side="left", padx=1)

        # Right: combo editor
        ce = ttk.Frame(combo_top)
        ce.pack(side="left", fill="both", expand=True, padx=8)
        self.combo_name = tk.StringVar()
        self.combo_notes = tk.StringVar()
        ttk.Label(ce, text="Combo Name").grid(row=0, column=0, sticky="w", padx=2)
        ttk.Entry(ce, textvariable=self.combo_name, width=20).grid(row=0, column=1, sticky="w", padx=2)
        ttk.Label(ce, text="Notes").grid(row=0, column=2, sticky="w", padx=2)
        ttk.Entry(ce, textvariable=self.combo_notes, width=30).grid(row=0, column=3, sticky="w", padx=2)

        # Hits inside the selected combo
        cols_c = ("talent", "offset", "reaction", "count", "snap_off")
        self.combo_hits_tree = ttk.Treeview(ce, columns=cols_c, show="headings", height=5)
        for c, w, h in zip(cols_c, (120, 70, 110, 50, 70),
                           ("Talent", "Time offset", "Reaction", "Count", "Snap offset")):
            self.combo_hits_tree.heading(c, text=h)
            self.combo_hits_tree.column(c, width=w, anchor="center")
        self.combo_hits_tree.grid(row=1, column=0, columnspan=4, sticky="nsew", pady=4)
        self.combo_hits_tree.bind("<<TreeviewSelect>>", self.on_combo_hit_select)
        ce.rowconfigure(1, weight=1)
        ce.columnconfigure(3, weight=1)

        # Combo-hit editor row
        che = ttk.Frame(ce)
        che.grid(row=2, column=0, columnspan=4, sticky="ew", pady=2)
        self.ch_talent = tk.StringVar()
        self.ch_offset = tk.StringVar(value="0")
        self.ch_reaction = tk.StringVar(value="None")
        self.ch_count = tk.StringVar(value="1")
        self.ch_snap_offset = tk.StringVar(value="")  # empty = no snapshot override

        ttk.Label(che, text="Talent").pack(side="left", padx=2)
        self.ch_talent_cb = ttk.Combobox(che, textvariable=self.ch_talent, width=14, state="readonly")
        self.ch_talent_cb.pack(side="left", padx=2)
        ttk.Label(che, text="Offset (s)").pack(side="left", padx=2)
        ttk.Entry(che, textvariable=self.ch_offset, width=7).pack(side="left", padx=2)
        ttk.Label(che, text="Reaction").pack(side="left", padx=2)
        ttk.Combobox(che, textvariable=self.ch_reaction,
                     values=[r.value for r in ReactionType], width=14, state="readonly").pack(side="left", padx=2)
        ttk.Label(che, text="Count").pack(side="left", padx=2)
        ttk.Entry(che, textvariable=self.ch_count, width=5).pack(side="left", padx=2)
        ttk.Label(che, text="Snap offset").pack(side="left", padx=2)
        ttk.Entry(che, textvariable=self.ch_snap_offset, width=6).pack(side="left", padx=2)

        chb = ttk.Frame(ce)
        chb.grid(row=3, column=0, columnspan=4, sticky="w", pady=2)
        ttk.Button(chb, text="Add / Update Hit in Combo", command=self.add_combo_hit).pack(side="left", padx=2)
        ttk.Button(chb, text="Remove Hit", command=self.remove_combo_hit).pack(side="left", padx=2)
        ttk.Button(chb, text="Save Combo", command=self.save_char_combo).pack(side="left", padx=8)

        self._char_combos: List[Combo] = []
        self._editing_combo_hits: List[ComboHit] = []  # hits of the combo currently being edited

        ttk.Button(right, text="Save Character", command=self.save_character).pack(pady=8)

    def refresh_char_list(self):
        self.char_listbox.delete(0, tk.END)
        for name in sorted(self.store.characters):
            self.char_listbox.insert(tk.END, name)
        self.char_weapon_cb["values"] = [""] + sorted(self.store.weapons.keys())
        self.char_artifact_cb["values"] = [""] + sorted(self.store.artifacts.keys())

    def _reload_char_talent_tree(self):
        self.char_talent_tree.delete(*self.char_talent_tree.get_children())
        for t in self._char_talents:
            self.char_talent_tree.insert("", tk.END, values=(
                t.name, f"{t.multiplier:.4g}", t.talent_type, t.element, t.scaling_stat,
                "Yes" if t.snapshots else ""
            ))

    def on_char_talent_select(self, event=None):
        sel = self.char_talent_tree.selection()
        if not sel:
            return
        vals = self.char_talent_tree.item(sel[0], "values")
        self.ct_name.set(vals[0])
        self.ct_mult.set(vals[1])
        self.ct_type.set(vals[2])
        self.ct_element.set(vals[3])
        self.ct_scaling.set(vals[4])
        self.ct_snapshots.set(vals[5] == "Yes")

    def add_char_talent(self):
        name = self.ct_name.get().strip()
        if not name:
            messagebox.showwarning("Missing name", "Talent name is required.")
            return
        try:
            mult = float(self.ct_mult.get() or 0)
        except ValueError:
            messagebox.showerror("Invalid", "Multiplier must be a number.")
            return
        th = TalentHit(
            name=name,
            multiplier=mult,
            talent_type=self.ct_type.get(),
            element=self.ct_element.get(),
            scaling_stat=self.ct_scaling.get(),
            snapshots=self.ct_snapshots.get(),
        )
        # Replace if same name exists
        self._char_talents = [t for t in self._char_talents if t.name != name]
        self._char_talents.append(th)
        self._reload_char_talent_tree()
        self.ch_talent_cb["values"] = [t.name for t in self._char_talents]

    def remove_char_talent(self):
        sel = self.char_talent_tree.selection()
        if not sel:
            return
        name = self.char_talent_tree.item(sel[0], "values")[0]
        self._char_talents = [t for t in self._char_talents if t.name != name]
        self._reload_char_talent_tree()
        # Keep combo talent dropdown in sync
        self.ch_talent_cb["values"] = [t.name for t in self._char_talents]

    # ── Combo helpers ───────────────────────────────────────────────────────
    def _reload_char_combo_list(self):
        self.char_combo_list.delete(0, tk.END)
        for c in self._char_combos:
            self.char_combo_list.insert(tk.END, f"{c.name}  ({len(c.hits)} hits)")

    def _reload_combo_hits_tree(self):
        self.combo_hits_tree.delete(*self.combo_hits_tree.get_children())
        for h in self._editing_combo_hits:
            snap = "" if h.snapshot_offset is None else f"{h.snapshot_offset:.3g}"
            self.combo_hits_tree.insert("", tk.END, values=(
                h.talent_name, f"{h.time_offset:.3g}", h.reaction, h.count, snap
            ))

    def new_char_combo(self):
        self.char_combo_list.selection_clear(0, tk.END)
        self.combo_name.set("")
        self.combo_notes.set("")
        self._editing_combo_hits = []
        self._reload_combo_hits_tree()
        self.ch_talent.set("")
        self.ch_offset.set("0")
        self.ch_reaction.set("None")
        self.ch_count.set("1")
        self.ch_snap_offset.set("")
        self.ch_talent_cb["values"] = [t.name for t in self._char_talents]

    def on_char_combo_select(self, event=None):
        sel = self.char_combo_list.curselection()
        if not sel:
            return
        idx = sel[0]
        if idx >= len(self._char_combos):
            return
        combo = self._char_combos[idx]
        self.combo_name.set(combo.name)
        self.combo_notes.set(combo.notes)
        self._editing_combo_hits = deepcopy(combo.hits)
        self._reload_combo_hits_tree()
        self.ch_talent_cb["values"] = [t.name for t in self._char_talents]

    def on_combo_hit_select(self, event=None):
        sel = self.combo_hits_tree.selection()
        if not sel:
            return
        vals = self.combo_hits_tree.item(sel[0], "values")
        self.ch_talent.set(vals[0])
        self.ch_offset.set(vals[1])
        self.ch_reaction.set(vals[2])
        self.ch_count.set(vals[3])
        self.ch_snap_offset.set(vals[4])

    def add_combo_hit(self):
        talent = self.ch_talent.get().strip()
        if not talent:
            messagebox.showwarning("Missing", "Select a talent for the combo hit.")
            return
        try:
            offset = float(self.ch_offset.get() or 0)
            count = int(self.ch_count.get() or 1)
            snap_s = self.ch_snap_offset.get().strip()
            snap = float(snap_s) if snap_s else None
        except ValueError:
            messagebox.showerror("Invalid", "Offset / count / snap offset must be numbers.")
            return
        ch = ComboHit(
            talent_name=talent,
            time_offset=offset,
            reaction=self.ch_reaction.get(),
            count=count,
            snapshot_offset=snap,
        )
        # Replace existing hit with same talent+offset, else append
        self._editing_combo_hits = [
            h for h in self._editing_combo_hits
            if not (h.talent_name == talent and abs(h.time_offset - offset) < 1e-6)
        ]
        self._editing_combo_hits.append(ch)
        self._editing_combo_hits.sort(key=lambda h: h.time_offset)
        self._reload_combo_hits_tree()

    def remove_combo_hit(self):
        sel = self.combo_hits_tree.selection()
        if not sel:
            return
        vals = self.combo_hits_tree.item(sel[0], "values")
        talent, offset = vals[0], float(vals[1])
        self._editing_combo_hits = [
            h for h in self._editing_combo_hits
            if not (h.talent_name == talent and abs(h.time_offset - offset) < 1e-6)
        ]
        self._reload_combo_hits_tree()

    def save_char_combo(self):
        name = self.combo_name.get().strip()
        if not name:
            messagebox.showwarning("Missing name", "Combo name is required.")
            return
        if not self._editing_combo_hits:
            messagebox.showwarning("Empty", "Add at least one hit to the combo.")
            return
        combo = Combo(
            name=name,
            hits=deepcopy(self._editing_combo_hits),
            notes=self.combo_notes.get(),
        )
        # Replace if same name exists
        self._char_combos = [c for c in self._char_combos if c.name != name]
        self._char_combos.append(combo)
        self._reload_char_combo_list()
        self.status.set(f"Combo '{name}' saved on character (click Save Character to persist)")

    def delete_char_combo(self):
        sel = self.char_combo_list.curselection()
        if not sel:
            return
        idx = sel[0]
        if idx >= len(self._char_combos):
            return
        name = self._char_combos[idx].name
        if messagebox.askyesno("Delete", f"Delete combo '{name}'?"):
            del self._char_combos[idx]
            self._reload_char_combo_list()
            self.new_char_combo()

    def on_char_select(self, event=None):
        sel = self.char_listbox.curselection()
        if not sel:
            return
        name = self.char_listbox.get(sel[0])
        c = self.store.characters[name]
        self.char_name.set(c.name)
        self.char_element.set(c.element)
        self.char_level.set(str(c.level))
        self.char_weapon.set(c.weapon_name)
        self.char_artifact.set(c.artifact_name)
        self.char_const.set(str(c.constellation))
        self.char_notes.set(c.notes)
        self.char_stats_editor.load(c.base_stats)
        self._char_talents = deepcopy(c.talents)
        self._reload_char_talent_tree()
        self.ct_element.set(c.element)
        # Combos
        self._char_combos = deepcopy(c.combos)
        self._reload_char_combo_list()
        self.new_char_combo()  # clear editor
        self.ch_talent_cb["values"] = [t.name for t in self._char_talents]

    def new_character(self):
        self.char_listbox.selection_clear(0, tk.END)
        self.char_name.set("")
        self.char_element.set("Pyro")
        self.char_level.set("90")
        self.char_weapon.set("")
        self.char_artifact.set("")
        self.char_const.set("0")
        self.char_notes.set("")
        self.char_stats_editor.load(Stats())
        self._char_talents = []
        self._reload_char_talent_tree()
        self.ct_name.set("")
        self.ct_mult.set("1.0")
        self.ct_type.set("Normal Attack")
        self.ct_element.set("Pyro")
        self.ct_scaling.set("atk")
        self.ct_snapshots.set(False)
        self._char_combos = []
        self._reload_char_combo_list()
        self.new_char_combo()
        self.ch_talent_cb["values"] = []

    def save_character(self):
        name = self.char_name.get().strip()
        if not name:
            messagebox.showwarning("Missing name", "Character name is required.")
            return
        try:
            c = Character(
                name=name,
                element=self.char_element.get(),
                level=int(self.char_level.get() or 90),
                base_stats=self.char_stats_editor.get(),
                weapon_name=self.char_weapon.get(),
                artifact_name=self.char_artifact.get(),
                talents=deepcopy(self._char_talents),
                combos=deepcopy(self._char_combos),
                constellation=int(self.char_const.get() or 0),
                notes=self.char_notes.get(),
            )
        except ValueError as e:
            messagebox.showerror("Invalid input", str(e))
            return

        old_name = None
        sel = self.char_listbox.curselection()
        if sel:
            old_name = self.char_listbox.get(sel[0])

        # Capture pre-state for undo (rename deletes old key)
        if old_name and old_name != name and old_name in self.store.characters:
            old_val = deepcopy(self.store.characters[old_name])
            preexisting = deepcopy(self.store.characters.get(name))
            del self.store.characters[old_name]
            self.store.characters[name] = c

            def undo():
                self.store.characters.pop(name, None)
                if preexisting is not None:
                    self.store.characters[name] = deepcopy(preexisting)
                self.store.characters[old_name] = deepcopy(old_val)
                self.refresh_all_lists()
                self.new_character()

            def redo():
                self.store.characters.pop(old_name, None)
                self.store.characters[name] = deepcopy(c)
                self.refresh_all_lists()

            self.undo_mgr.push(undo, redo, f"Rename character '{old_name}' → '{name}'")
        else:
            old_val = deepcopy(self.store.characters.get(name))
            self.store.characters[name] = c
            self._push_store_dict_undo(
                "characters", name, old_val, c,
                f"Save character '{name}'",
                on_change=lambda: (self.refresh_all_lists(), self.new_character()),
            )

        self.refresh_all_lists()
        self.status.set(f"Character '{name}' saved (remember to File → Save)")
        for i, n in enumerate(sorted(self.store.characters)):
            if n == name:
                self.char_listbox.selection_set(i)
                break

    def delete_character(self):
        sel = self.char_listbox.curselection()
        if not sel:
            return
        name = self.char_listbox.get(sel[0])
        if messagebox.askyesno("Delete", f"Delete character '{name}'?"):
            old_val = deepcopy(self.store.characters[name])
            del self.store.characters[name]
            self._push_store_dict_undo(
                "characters", name, old_val, None,
                f"Delete character '{name}'",
                on_change=lambda: (self.refresh_all_lists(), self.new_character()),
            )
            self.refresh_all_lists()
            self.new_character()
            self.status.set(f"Deleted '{name}'")

    # =========================================================================
    # WEAPONS TAB
    # =========================================================================
    def _build_weapons_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Weapons")

        left = ttk.Frame(tab)
        left.pack(side="left", fill="y", padx=6, pady=6)
        ttk.Label(left, text="Weapons", font=("", 11, "bold")).pack(anchor="w")
        self.weapon_listbox = tk.Listbox(left, width=28, height=25, exportselection=False)
        self.weapon_listbox.pack(fill="y", expand=True)
        self.weapon_listbox.bind("<<ListboxSelect>>", self.on_weapon_select)
        bf = ttk.Frame(left)
        bf.pack(fill="x", pady=4)
        ttk.Button(bf, text="New", command=self.new_weapon).pack(side="left", padx=2)
        ttk.Button(bf, text="Delete", command=self.delete_weapon).pack(side="left", padx=2)

        right_container, right, _wpn_canvas = make_scrollable(tab, bg=self.colors["bg"])
        right_container.pack(side="left", fill="both", expand=True, padx=6, pady=6)

        form = ttk.LabelFrame(right, text="Weapon Details")
        form.pack(fill="x", pady=4)
        self.wpn_name = tk.StringVar()
        self.wpn_base = tk.StringVar(value="0")
        self.wpn_sub_type = tk.StringVar(value="atk_pct")
        self.wpn_sub_val = tk.StringVar(value="0")
        self.wpn_notes = tk.StringVar()

        ttk.Label(form, text="Name").grid(row=0, column=0, sticky="w", padx=4, pady=2)
        ttk.Entry(form, textvariable=self.wpn_name, width=30).grid(row=0, column=1, sticky="w", padx=4)
        ttk.Label(form, text="Base ATK").grid(row=1, column=0, sticky="w", padx=4, pady=2)
        ttk.Entry(form, textvariable=self.wpn_base, width=12).grid(row=1, column=1, sticky="w", padx=4)
        ttk.Label(form, text="Substat Type").grid(row=2, column=0, sticky="w", padx=4, pady=2)
        ttk.Combobox(form, textvariable=self.wpn_sub_type, width=18,
                     values=["atk_pct", "hp_pct", "def_pct", "em", "er", "crit_rate", "crit_dmg",
                             "pyro_dmg", "hydro_dmg", "electro_dmg", "cryo_dmg", "anemo_dmg",
                             "geo_dmg", "dendro_dmg", "physical_dmg"]).grid(row=2, column=1, sticky="w", padx=4)
        ttk.Label(form, text="Substat Value").grid(row=3, column=0, sticky="w", padx=4, pady=2)
        ttk.Entry(form, textvariable=self.wpn_sub_val, width=12).grid(row=3, column=1, sticky="w", padx=4)
        ttk.Label(form, text="Notes").grid(row=4, column=0, sticky="w", padx=4, pady=2)
        ttk.Entry(form, textvariable=self.wpn_notes, width=40).grid(row=4, column=1, sticky="w", padx=4)

        self.wpn_passive_editor = StatsEditor(right, title="Passive Stats (always-on or average)")
        self.wpn_passive_editor.pack(fill="x", pady=6)

        ttk.Button(right, text="Save Weapon", command=self.save_weapon).pack(pady=8)

    def refresh_weapon_list(self):
        self.weapon_listbox.delete(0, tk.END)
        for name in sorted(self.store.weapons):
            self.weapon_listbox.insert(tk.END, name)

    def on_weapon_select(self, event=None):
        sel = self.weapon_listbox.curselection()
        if not sel:
            return
        w = self.store.weapons[self.weapon_listbox.get(sel[0])]
        self.wpn_name.set(w.name)
        self.wpn_base.set(str(w.base_atk))
        self.wpn_sub_type.set(w.substat_type)
        self.wpn_sub_val.set(str(w.substat_value))
        self.wpn_notes.set(w.notes)
        self.wpn_passive_editor.load(w.passive)

    def new_weapon(self):
        self.weapon_listbox.selection_clear(0, tk.END)
        self.wpn_name.set("")
        self.wpn_base.set("0")
        self.wpn_sub_type.set("atk_pct")
        self.wpn_sub_val.set("0")
        self.wpn_notes.set("")
        self.wpn_passive_editor.load(Stats())

    def save_weapon(self):
        name = self.wpn_name.get().strip()
        if not name:
            messagebox.showwarning("Missing name", "Weapon name is required.")
            return
        try:
            w = Weapon(
                name=name,
                base_atk=float(self.wpn_base.get() or 0),
                substat_type=self.wpn_sub_type.get(),
                substat_value=float(self.wpn_sub_val.get() or 0),
                passive=self.wpn_passive_editor.get(),
                notes=self.wpn_notes.get(),
            )
        except ValueError as e:
            messagebox.showerror("Invalid input", str(e))
            return
        old_val = deepcopy(self.store.weapons.get(name))
        self.store.weapons[name] = w
        self._push_store_dict_undo(
            "weapons", name, old_val, w, f"Save weapon '{name}'",
            on_change=lambda: (self.refresh_weapon_list(), self.refresh_char_list()),
        )
        self.refresh_weapon_list()
        self.refresh_char_list()  # update comboboxes
        self.status.set(f"Weapon '{name}' saved")

    def delete_weapon(self):
        sel = self.weapon_listbox.curselection()
        if not sel:
            return
        name = self.weapon_listbox.get(sel[0])
        if messagebox.askyesno("Delete", f"Delete weapon '{name}'?"):
            old_val = deepcopy(self.store.weapons[name])
            del self.store.weapons[name]
            self._push_store_dict_undo(
                "weapons", name, old_val, None, f"Delete weapon '{name}'",
                on_change=lambda: (self.refresh_weapon_list(), self.new_weapon()),
            )
            self.refresh_weapon_list()
            self.new_weapon()

    # =========================================================================
    # ARTIFACTS TAB
    # =========================================================================
    def _build_artifacts_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Artifacts")

        left = ttk.Frame(tab)
        left.pack(side="left", fill="y", padx=6, pady=6)
        ttk.Label(left, text="Artifact Builds", font=("", 11, "bold")).pack(anchor="w")
        self.art_listbox = tk.Listbox(left, width=28, height=25, exportselection=False)
        self.art_listbox.pack(fill="y", expand=True)
        self.art_listbox.bind("<<ListboxSelect>>", self.on_artifact_select)
        bf = ttk.Frame(left)
        bf.pack(fill="x", pady=4)
        ttk.Button(bf, text="New", command=self.new_artifact).pack(side="left", padx=2)
        ttk.Button(bf, text="Delete", command=self.delete_artifact).pack(side="left", padx=2)

        right_container, right, _art_canvas = make_scrollable(tab, bg=self.colors["bg"])
        right_container.pack(side="left", fill="both", expand=True, padx=6, pady=6)

        form = ttk.LabelFrame(right, text="Artifact Build Name")
        form.pack(fill="x", pady=4)
        self.art_name = tk.StringVar()
        self.art_notes = tk.StringVar()
        ttk.Label(form, text="Name").grid(row=0, column=0, sticky="w", padx=4)
        ttk.Entry(form, textvariable=self.art_name, width=30).grid(row=0, column=1, sticky="w", padx=4)
        ttk.Label(form, text="Notes").grid(row=1, column=0, sticky="w", padx=4)
        ttk.Entry(form, textvariable=self.art_notes, width=40).grid(row=1, column=1, sticky="w", padx=4)

        # KQM Standard preset
        kqm = ttk.LabelFrame(right, text="KQM Standard Preset (one-click investment)")
        kqm.pack(fill="x", pady=6)
        self.kqm_sands = tk.StringVar(value="atk_pct")
        self.kqm_goblet = tk.StringVar(value="elem_dmg")
        self.kqm_circlet = tk.StringVar(value="crit_rate")
        self.kqm_element = tk.StringVar(value="Pyro")
        self.kqm_extra = tk.StringVar(value="0")
        self.kqm_priority = tk.StringVar(value="crit_rate,crit_dmg,atk_pct")

        ttk.Label(kqm, text="Sands").grid(row=0, column=0, padx=3, sticky="w")
        ttk.Combobox(kqm, textvariable=self.kqm_sands, width=10, state="readonly",
                     values=["atk_pct", "hp_pct", "def_pct", "em", "er"]).grid(row=0, column=1, padx=3)
        ttk.Label(kqm, text="Goblet").grid(row=0, column=2, padx=3, sticky="w")
        ttk.Combobox(kqm, textvariable=self.kqm_goblet, width=12, state="readonly",
                     values=["elem_dmg", "physical_dmg", "atk_pct", "hp_pct", "em"]).grid(row=0, column=3, padx=3)
        ttk.Label(kqm, text="Circlet").grid(row=0, column=4, padx=3, sticky="w")
        ttk.Combobox(kqm, textvariable=self.kqm_circlet, width=10, state="readonly",
                     values=["crit_rate", "crit_dmg", "atk_pct", "hp_pct", "em", "healing"]).grid(row=0, column=5, padx=3)
        ttk.Label(kqm, text="Element").grid(row=1, column=0, padx=3, sticky="w")
        ttk.Combobox(kqm, textvariable=self.kqm_element, width=10, state="readonly",
                     values=[e.value for e in Element]).grid(row=1, column=1, padx=3)
        ttk.Label(kqm, text="Extra useful rolls").grid(row=1, column=2, padx=3, sticky="w")
        ttk.Entry(kqm, textvariable=self.kqm_extra, width=6).grid(row=1, column=3, padx=3, sticky="w")
        ttk.Label(kqm, text="Priority (comma)").grid(row=1, column=4, padx=3, sticky="w")
        ttk.Entry(kqm, textvariable=self.kqm_priority, width=28).grid(row=1, column=5, padx=3)
        bf = ttk.Frame(kqm)
        bf.grid(row=2, column=0, columnspan=6, pady=4, sticky="w")
        ttk.Button(bf, text="Apply KQM Standard", command=lambda: self.apply_kqm(0)).pack(side="left", padx=4)
        ttk.Button(bf, text="KQM +5", command=lambda: self.apply_kqm(5)).pack(side="left", padx=4)
        ttk.Button(bf, text="KQM +10", command=lambda: self.apply_kqm(10)).pack(side="left", padx=4)
        ttk.Label(kqm, text="Uses 40 rolls (20 fixed + 20 distributed). +N adds N more distributed rolls on priority stats.",
                  foreground="#666").grid(row=3, column=0, columnspan=6, sticky="w", padx=4)

        self.art_main_editor = StatsEditor(right, title="Main Stats (Flower/Plume/Sands/Goblet/Circlet)")
        self.art_main_editor.pack(fill="x", pady=4)
        self.art_sub_editor = StatsEditor(right, title="Sub Stats (total of all subs)")
        self.art_sub_editor.pack(fill="x", pady=4)
        self.art_2pc_editor = StatsEditor(right, title="2-Piece Set Bonus")
        self.art_2pc_editor.pack(fill="x", pady=4)
        self.art_4pc_editor = StatsEditor(right, title="4-Piece Set Bonus (always-on part)")
        self.art_4pc_editor.pack(fill="x", pady=4)

        ttk.Button(right, text="Save Artifact Build", command=self.save_artifact).pack(pady=8)

    def refresh_artifact_list(self):
        self.art_listbox.delete(0, tk.END)
        for name in sorted(self.store.artifacts):
            self.art_listbox.insert(tk.END, name)

    def on_artifact_select(self, event=None):
        sel = self.art_listbox.curselection()
        if not sel:
            return
        a = self.store.artifacts[self.art_listbox.get(sel[0])]
        self.art_name.set(a.name)
        self.art_notes.set(a.notes)
        self.art_main_editor.load(a.main_stats)
        self.art_sub_editor.load(a.sub_stats)
        self.art_2pc_editor.load(a.set_2pc)
        self.art_4pc_editor.load(a.set_4pc)

    def new_artifact(self):
        self.art_listbox.selection_clear(0, tk.END)
        self.art_name.set("")
        self.art_notes.set("")
        self.art_main_editor.load(Stats())
        self.art_sub_editor.load(Stats())
        self.art_2pc_editor.load(Stats())
        self.art_4pc_editor.load(Stats())

    def apply_kqm(self, extra: int = 0):
        try:
            extra_n = int(self.kqm_extra.get() or 0) + extra
        except ValueError:
            extra_n = extra
        prio = [x.strip() for x in self.kqm_priority.get().split(",") if x.strip()]
        if not prio:
            prio = ["crit_rate", "crit_dmg", "atk_pct"]
        main, sub = build_kqm_stats(
            sands=self.kqm_sands.get(),
            goblet=self.kqm_goblet.get(),
            circlet=self.kqm_circlet.get(),
            element=self.kqm_element.get(),
            extra_useful_rolls=extra_n,
            useful_priority=prio,
        )
        self.art_main_editor.load(main)
        self.art_sub_editor.load(sub)
        label = "KQM Standard" if extra_n == 0 else f"KQM +{extra_n}"
        if not self.art_name.get().strip():
            self.art_name.set(f"{label} {self.kqm_element.get()}")
        self.art_notes.set(f"{label} | sands={self.kqm_sands.get()} goblet={self.kqm_goblet.get()} "
                           f"circlet={self.kqm_circlet.get()} priority={','.join(prio)}")
        self.status.set(f"Applied {label} stats – review and Save Artifact Build")

    def save_artifact(self):
        name = self.art_name.get().strip()
        if not name:
            messagebox.showwarning("Missing name", "Artifact build name is required.")
            return
        a = Artifact(
            name=name,
            main_stats=self.art_main_editor.get(),
            sub_stats=self.art_sub_editor.get(),
            set_2pc=self.art_2pc_editor.get(),
            set_4pc=self.art_4pc_editor.get(),
            notes=self.art_notes.get(),
        )
        old_val = deepcopy(self.store.artifacts.get(name))
        self.store.artifacts[name] = a
        self._push_store_dict_undo(
            "artifacts", name, old_val, a, f"Save artifact '{name}'",
            on_change=lambda: (self.refresh_artifact_list(), self.refresh_char_list()),
        )
        self.refresh_artifact_list()
        self.refresh_char_list()
        self.status.set(f"Artifact build '{name}' saved")

    def delete_artifact(self):
        sel = self.art_listbox.curselection()
        if not sel:
            return
        name = self.art_listbox.get(sel[0])
        if messagebox.askyesno("Delete", f"Delete artifact build '{name}'?"):
            old_val = deepcopy(self.store.artifacts[name])
            del self.store.artifacts[name]
            self._push_store_dict_undo(
                "artifacts", name, old_val, None, f"Delete artifact '{name}'",
                on_change=lambda: (self.refresh_artifact_list(), self.new_artifact()),
            )
            self.refresh_artifact_list()
            self.new_artifact()

    # =========================================================================
    # BUFF TEMPLATES TAB
    # =========================================================================
    def _build_buffs_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Buff Templates")

        left = ttk.Frame(tab)
        left.pack(side="left", fill="y", padx=6, pady=6)
        ttk.Label(left, text="Buff Templates", font=("", 11, "bold")).pack(anchor="w")
        self.buff_listbox = tk.Listbox(left, width=28, height=25, exportselection=False)
        self.buff_listbox.pack(fill="y", expand=True)
        self.buff_listbox.bind("<<ListboxSelect>>", self.on_buff_select)
        bf = ttk.Frame(left)
        bf.pack(fill="x", pady=4)
        ttk.Button(bf, text="New", command=self.new_buff).pack(side="left", padx=2)
        ttk.Button(bf, text="Delete", command=self.delete_buff).pack(side="left", padx=2)

        right_container, right, _buff_canvas = make_scrollable(tab, bg=self.colors["bg"])
        right_container.pack(side="left", fill="both", expand=True, padx=6, pady=6)

        form = ttk.LabelFrame(right, text="Buff Template")
        form.pack(fill="x", pady=4)
        self.buff_name = tk.StringVar()
        self.buff_duration = tk.StringVar(value="10")
        self.buff_notes = tk.StringVar()
        ttk.Label(form, text="Name").grid(row=0, column=0, sticky="w", padx=4)
        ttk.Entry(form, textvariable=self.buff_name, width=30).grid(row=0, column=1, sticky="w", padx=4)
        ttk.Label(form, text="Default Duration (s)").grid(row=1, column=0, sticky="w", padx=4)
        ttk.Entry(form, textvariable=self.buff_duration, width=10).grid(row=1, column=1, sticky="w", padx=4)
        ttk.Label(form, text="Notes").grid(row=2, column=0, sticky="w", padx=4)
        ttk.Entry(form, textvariable=self.buff_notes, width=40).grid(row=2, column=1, sticky="w", padx=4)

        # Talent type filter – empty = applies to everything
        ttk.Label(form, text="Applies to talent types").grid(row=3, column=0, sticky="nw", padx=4, pady=4)
        tf = ttk.Frame(form)
        tf.grid(row=3, column=1, sticky="w", padx=4, pady=4)
        self.buff_talent_vars: Dict[str, tk.BooleanVar] = {}
        for i, tt in enumerate(TALENT_TYPES):
            var = tk.BooleanVar(value=False)
            ttk.Checkbutton(tf, text=tt, variable=var).grid(row=i // 3, column=i % 3, sticky="w", padx=4)
            self.buff_talent_vars[tt] = var
        ttk.Label(form, text="(leave all unchecked = applies to every talent type)",
                  foreground="#666").grid(row=4, column=0, columnspan=2, sticky="w", padx=4)

        # Provider-scaled section (anti-loop: permanent stats only)
        prov = ttk.LabelFrame(right, text="Provider-scaled value (optional) — uses provider PERMANENT stats only, never team buffs")
        prov.pack(fill="x", pady=6)
        self.buff_provider = tk.StringVar()
        self.buff_provider_stat = tk.StringVar(value="none")
        self.buff_provider_mult = tk.StringVar(value="1.0")
        self.buff_provider_target = tk.StringVar(value="flat_atk")

        ttk.Label(prov, text="Provider character").grid(row=0, column=0, sticky="w", padx=4, pady=2)
        self.buff_provider_cb = ttk.Combobox(prov, textvariable=self.buff_provider, width=18)
        self.buff_provider_cb.grid(row=0, column=1, sticky="w", padx=4)
        ttk.Label(prov, text="Stat to read").grid(row=0, column=2, sticky="w", padx=4)
        ttk.Combobox(prov, textvariable=self.buff_provider_stat, values=PROVIDER_STAT_CHOICES,
                     width=14, state="readonly").grid(row=0, column=3, sticky="w", padx=4)
        ttk.Label(prov, text="Multiplier").grid(row=1, column=0, sticky="w", padx=4, pady=2)
        ttk.Entry(prov, textvariable=self.buff_provider_mult, width=10).grid(row=1, column=1, sticky="w", padx=4)
        ttk.Label(prov, text="Apply as").grid(row=1, column=2, sticky="w", padx=4)
        ttk.Combobox(prov, textvariable=self.buff_provider_target,
                     values=["flat_atk", "flat_hp", "flat_def", "em", "atk_pct", "hp_pct", "def_pct", "additive_base"],
                     width=14, state="readonly").grid(row=1, column=3, sticky="w", padx=4)
        ttk.Label(prov, text="Examples: Bennett → base_atk × talent% → flat_atk;  "
                             "Shenhe-style quills → personal_atk × % → additive_base",
                  foreground="#666").grid(row=2, column=0, columnspan=4, sticky="w", padx=4, pady=2)

        self.buff_stats_editor = StatsEditor(right, title="Fixed Buff Stats (added on top of any provider-scaled value)")
        self.buff_stats_editor.pack(fill="x", pady=6)

        ttk.Button(right, text="Save Buff Template", command=self.save_buff).pack(pady=8)

    def refresh_buff_list(self):
        self.buff_listbox.delete(0, tk.END)
        for name in sorted(self.store.buff_templates):
            self.buff_listbox.insert(tk.END, name)
        if hasattr(self, "buff_provider_cb"):
            self.buff_provider_cb["values"] = [""] + sorted(self.store.characters.keys())

    def on_buff_select(self, event=None):
        sel = self.buff_listbox.curselection()
        if not sel:
            return
        b = self.store.buff_templates[self.buff_listbox.get(sel[0])]
        self.buff_name.set(b.name)
        self.buff_duration.set(str(b.default_duration))
        self.buff_notes.set(b.notes)
        self.buff_stats_editor.load(b.stats)
        for tt, var in self.buff_talent_vars.items():
            var.set(tt in b.talent_types)
        self.buff_provider.set(b.provider_name)
        self.buff_provider_stat.set(b.provider_stat or "none")
        self.buff_provider_mult.set(str(b.provider_multiplier))
        self.buff_provider_target.set(b.provider_target or "flat_atk")

    def new_buff(self):
        self.buff_listbox.selection_clear(0, tk.END)
        self.buff_name.set("")
        self.buff_duration.set("10")
        self.buff_notes.set("")
        self.buff_stats_editor.load(Stats())
        for var in self.buff_talent_vars.values():
            var.set(False)
        self.buff_provider.set("")
        self.buff_provider_stat.set("none")
        self.buff_provider_mult.set("1.0")
        self.buff_provider_target.set("flat_atk")

    def save_buff(self):
        name = self.buff_name.get().strip()
        if not name:
            messagebox.showwarning("Missing name", "Buff name is required.")
            return
        try:
            talent_types = [tt for tt, var in self.buff_talent_vars.items() if var.get()]
            b = BuffTemplate(
                name=name,
                stats=self.buff_stats_editor.get(),
                default_duration=float(self.buff_duration.get() or 10),
                talent_types=talent_types,
                notes=self.buff_notes.get(),
                provider_name=self.buff_provider.get().strip(),
                provider_stat=self.buff_provider_stat.get() or "none",
                provider_multiplier=float(self.buff_provider_mult.get() or 1.0),
                provider_target=self.buff_provider_target.get() or "flat_atk",
            )
        except ValueError as e:
            messagebox.showerror("Invalid input", str(e))
            return
        old_val = deepcopy(self.store.buff_templates.get(name))
        self.store.buff_templates[name] = b
        self._push_store_dict_undo(
            "buff_templates", name, old_val, b, f"Save buff '{name}'",
            on_change=self.refresh_buff_list,
        )
        self.refresh_buff_list()
        self.status.set(f"Buff template '{name}' saved")

    def delete_buff(self):
        sel = self.buff_listbox.curselection()
        if not sel:
            return
        name = self.buff_listbox.get(sel[0])
        if messagebox.askyesno("Delete", f"Delete buff template '{name}'?"):
            old_val = deepcopy(self.store.buff_templates[name])
            del self.store.buff_templates[name]
            self._push_store_dict_undo(
                "buff_templates", name, old_val, None, f"Delete buff '{name}'",
                on_change=lambda: (self.refresh_buff_list(), self.new_buff()),
            )
            self.refresh_buff_list()
            self.new_buff()

    # =========================================================================
    # ROTATIONS TAB
    # =========================================================================
    def _build_rotations_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Rotations")

        # Whole tab scrolls so nothing is clipped at the bottom
        outer, body, self._rot_canvas = make_scrollable(tab, bg=self.colors["bg"])
        outer.pack(fill="both", expand=True, padx=4, pady=4)

        # Top: rotation list + basic info
        top = ttk.Frame(body)
        top.pack(fill="x", padx=6, pady=4)

        left = ttk.Frame(top)
        left.pack(side="left", fill="y")
        ttk.Label(left, text="Rotations", style="Header.TLabel").pack(anchor="w")
        self.rot_listbox = tk.Listbox(left, width=25, height=6, exportselection=False)
        self.rot_listbox.pack()
        self.rot_listbox.bind("<<ListboxSelect>>", self.on_rotation_select)
        bf = ttk.Frame(left)
        bf.pack(fill="x", pady=2)
        ttk.Button(bf, text="New", command=self.new_rotation).pack(side="left", padx=2)
        ttk.Button(bf, text="Delete", style="Danger.TButton",
                   command=self.delete_rotation).pack(side="left", padx=2)

        info = ttk.LabelFrame(top, text="Rotation Info")
        info.pack(side="left", fill="x", expand=True, padx=8)
        self.rot_name = tk.StringVar()
        self.rot_duration = tk.StringVar(value="20")
        self.rot_notes = tk.StringVar()
        ttk.Label(info, text="Name").grid(row=0, column=0, sticky="w", padx=4)
        ttk.Entry(info, textvariable=self.rot_name, width=25).grid(row=0, column=1, sticky="w", padx=4)
        ttk.Label(info, text="Duration (s)").grid(row=1, column=0, sticky="w", padx=4)
        ttk.Entry(info, textvariable=self.rot_duration, width=10).grid(row=1, column=1, sticky="w", padx=4)
        ttk.Label(info, text="Notes").grid(row=2, column=0, sticky="w", padx=4)
        ttk.Entry(info, textvariable=self.rot_notes, width=40).grid(row=2, column=1, sticky="w", padx=4)
        ttk.Button(info, text="Save Rotation", style="Accent.TButton",
                   command=self.save_rotation).grid(row=0, column=2, rowspan=3, padx=10)

        # Bottom: Hits and Timed Buffs side by side
        bottom = ttk.Frame(body)
        bottom.pack(fill="both", expand=True, padx=6, pady=4)

        # ── Hits panel ──────────────────────────────────────────────────────
        hits_frame = ttk.LabelFrame(
            bottom,
            text="Hits  (select a combo group row to delete the whole combo)",
        )
        hits_frame.pack(side="left", fill="both", expand=True, padx=4)

        cols = ("time", "character", "talent", "type", "element", "reaction", "snap", "count")
        tree_wrap = ttk.Frame(hits_frame)
        tree_wrap.pack(fill="both", expand=True)
        self.hits_tree = ttk.Treeview(
            tree_wrap, columns=cols, show="tree headings", height=10, selectmode="extended"
        )
        hits_scroll = ttk.Scrollbar(tree_wrap, orient="vertical", command=self.hits_tree.yview)
        self.hits_tree.configure(yscrollcommand=hits_scroll.set)

        self.hits_tree.heading("#0", text="")
        self.hits_tree.column("#0", width=22, stretch=False)
        for c, w, h in zip(cols, (50, 90, 110, 100, 70, 120, 50, 45),
                           ("Time", "Character", "Talent", "Type", "Element", "Reaction", "Snap", "Count")):
            self.hits_tree.heading(c, text=h)
            self.hits_tree.column(c, width=w, anchor="center")
        self.hits_tree.pack(side="left", fill="both", expand=True)
        hits_scroll.pack(side="right", fill="y")
        self.hits_tree.bind("<<TreeviewSelect>>", self.on_hit_select)
        bind_mousewheel(self.hits_tree)

        # Maps tree item iid → ("group", group_id) or ("hit", index_in__current_hits)
        self._hits_tree_map: Dict[str, Tuple[str, Any]] = {}

        hit_btn = ttk.Frame(hits_frame)
        hit_btn.pack(fill="x", pady=2)
        ttk.Button(hit_btn, text="Add Hit", command=self.add_hit).pack(side="left", padx=2)
        ttk.Button(hit_btn, text="Update Hit", command=self.update_hit).pack(side="left", padx=2)
        ttk.Button(hit_btn, text="Delete Selected", style="Danger.TButton",
                   command=self.remove_hit).pack(side="left", padx=2)
        ttk.Label(hit_btn, text="  (group row = whole combo)", style="Hint.TLabel").pack(side="left", padx=4)

        # Insert Combo row
        combo_ins = ttk.Frame(hits_frame)
        combo_ins.pack(fill="x", pady=3)
        ttk.Label(combo_ins, text="Insert Combo:").pack(side="left", padx=2)
        self.ins_combo_char = tk.StringVar()
        self.ins_combo_name = tk.StringVar()
        self.ins_combo_start = tk.StringVar(value="0")
        self.ins_combo_char_cb = ttk.Combobox(combo_ins, textvariable=self.ins_combo_char, width=12)
        self.ins_combo_char_cb.pack(side="left", padx=2)
        self.ins_combo_char_cb.bind("<<ComboboxSelected>>", self.on_ins_combo_char_changed)
        self.ins_combo_cb = ttk.Combobox(combo_ins, textvariable=self.ins_combo_name, width=16, state="readonly")
        self.ins_combo_cb.pack(side="left", padx=2)
        ttk.Label(combo_ins, text="at t=").pack(side="left")
        ttk.Entry(combo_ins, textvariable=self.ins_combo_start, width=6).pack(side="left", padx=2)
        ttk.Button(combo_ins, text="Insert Combo → Hits", command=self.insert_combo).pack(side="left", padx=4)

        # Hit editor
        hit_edit = ttk.LabelFrame(hits_frame, text="Hit editor")
        hit_edit.pack(fill="x", pady=4)
        self.hit_time = tk.StringVar(value="0")
        self.hit_char = tk.StringVar()
        self.hit_talent_name = tk.StringVar()
        self.hit_reaction = tk.StringVar(value="None")
        self.hit_count = tk.StringVar(value="1")
        self.hit_additive = tk.StringVar(value="0")
        self.hit_transform = tk.BooleanVar(value=False)
        self.hit_snapshot_time = tk.StringVar(value="")

        ttk.Label(hit_edit, text="Time (s)").grid(row=0, column=0, sticky="w", padx=2, pady=2)
        ttk.Entry(hit_edit, textvariable=self.hit_time, width=8).grid(row=0, column=1, padx=2)
        ttk.Label(hit_edit, text="Character").grid(row=0, column=2, sticky="w", padx=2)
        self.hit_char_cb = ttk.Combobox(hit_edit, textvariable=self.hit_char, width=14)
        self.hit_char_cb.grid(row=0, column=3, padx=2)
        self.hit_char_cb.bind("<<ComboboxSelected>>", self.on_hit_char_changed)

        ttk.Label(hit_edit, text="Talent").grid(row=0, column=4, sticky="w", padx=2)
        self.hit_talent_cb = ttk.Combobox(hit_edit, textvariable=self.hit_talent_name, width=18, state="readonly")
        self.hit_talent_cb.grid(row=0, column=5, padx=2)

        ttk.Label(hit_edit, text="Reaction").grid(row=1, column=0, sticky="w", padx=2, pady=2)
        ttk.Combobox(hit_edit, textvariable=self.hit_reaction,
                     values=[r.value for r in ReactionType], width=22, state="readonly").grid(
            row=1, column=1, columnspan=2, padx=2)
        ttk.Label(hit_edit, text="Count").grid(row=1, column=3, sticky="w", padx=2)
        ttk.Entry(hit_edit, textvariable=self.hit_count, width=6).grid(row=1, column=4, padx=2)

        ttk.Label(hit_edit, text="Snapshot Time").grid(row=2, column=0, sticky="w", padx=2, pady=2)
        ttk.Entry(hit_edit, textvariable=self.hit_snapshot_time, width=8).grid(row=2, column=1, padx=2)
        ttk.Label(hit_edit, text="(cast time; blank = dynamic)", style="Hint.TLabel").grid(
            row=2, column=2, columnspan=2, sticky="w", padx=2)
        ttk.Label(hit_edit, text="Additive").grid(row=3, column=0, sticky="w", padx=2)
        ttk.Entry(hit_edit, textvariable=self.hit_additive, width=8).grid(row=3, column=1, padx=2)
        ttk.Checkbutton(hit_edit, text="Force pure reaction dmg (ignore talent MV)",
                        variable=self.hit_transform).grid(row=3, column=2, columnspan=3, sticky="w", padx=2)

        ttk.Label(hit_edit, text="Extra contributors (Lunar-Charged / Stellar-Swirl blend)",
                  style="Hint.TLabel").grid(row=4, column=0, columnspan=6, sticky="w", padx=2, pady=(6, 0))
        self.hit_contrib1 = tk.StringVar()
        self.hit_contrib2 = tk.StringVar()
        self.hit_contrib3 = tk.StringVar()
        self.hit_contrib1_cb = ttk.Combobox(hit_edit, textvariable=self.hit_contrib1, width=14)
        self.hit_contrib2_cb = ttk.Combobox(hit_edit, textvariable=self.hit_contrib2, width=14)
        self.hit_contrib3_cb = ttk.Combobox(hit_edit, textvariable=self.hit_contrib3, width=14)
        ttk.Label(hit_edit, text="2nd").grid(row=5, column=0, sticky="w", padx=2, pady=2)
        self.hit_contrib1_cb.grid(row=5, column=1, padx=2)
        ttk.Label(hit_edit, text="3rd").grid(row=5, column=2, sticky="w", padx=2)
        self.hit_contrib2_cb.grid(row=5, column=3, padx=2)
        ttk.Label(hit_edit, text="4th").grid(row=5, column=4, sticky="w", padx=2)
        self.hit_contrib3_cb.grid(row=5, column=5, padx=2)

        # ── Timed Buffs panel ───────────────────────────────────────────────
        buffs_frame = ttk.LabelFrame(bottom, text="Timed Buffs in this Rotation")
        buffs_frame.pack(side="left", fill="both", expand=True, padx=4)
        bcols = ("template", "start", "duration")
        tb_wrap = ttk.Frame(buffs_frame)
        tb_wrap.pack(fill="both", expand=True)
        self.tbuff_tree = ttk.Treeview(tb_wrap, columns=bcols, show="headings", height=10)
        tb_scroll = ttk.Scrollbar(tb_wrap, orient="vertical", command=self.tbuff_tree.yview)
        self.tbuff_tree.configure(yscrollcommand=tb_scroll.set)
        for c, w in zip(bcols, (160, 70, 70)):
            self.tbuff_tree.heading(c, text=c.capitalize())
            self.tbuff_tree.column(c, width=w, anchor="center")
        self.tbuff_tree.pack(side="left", fill="both", expand=True)
        tb_scroll.pack(side="right", fill="y")
        bind_mousewheel(self.tbuff_tree)

        tb_btn = ttk.Frame(buffs_frame)
        tb_btn.pack(fill="x", pady=2)
        ttk.Button(tb_btn, text="Add Timed Buff", command=self.add_timed_buff).pack(side="left", padx=2)
        ttk.Button(tb_btn, text="Remove", style="Danger.TButton",
                   command=self.remove_timed_buff).pack(side="left", padx=2)

        tb_edit = ttk.Frame(buffs_frame)
        tb_edit.pack(fill="x", pady=4)
        self.tb_template = tk.StringVar()
        self.tb_start = tk.StringVar(value="0")
        self.tb_duration = tk.StringVar(value="10")
        ttk.Label(tb_edit, text="Template").grid(row=0, column=0, padx=2)
        self.tb_template_cb = ttk.Combobox(tb_edit, textvariable=self.tb_template, width=18)
        self.tb_template_cb.grid(row=0, column=1, padx=2)
        ttk.Label(tb_edit, text="Start").grid(row=0, column=2, padx=2)
        ttk.Entry(tb_edit, textvariable=self.tb_start, width=8).grid(row=0, column=3, padx=2)
        ttk.Label(tb_edit, text="Duration").grid(row=0, column=4, padx=2)
        ttk.Entry(tb_edit, textvariable=self.tb_duration, width=8).grid(row=0, column=5, padx=2)

        # Spacer so the scroll region has a little room under the last controls
        ttk.Frame(body, height=24).pack(fill="x")

        self._current_hits: List[Hit] = []
        self._current_tbuffs: List[TimedBuff] = []

    def refresh_rotation_list(self):
        self.rot_listbox.delete(0, tk.END)
        for name in sorted(self.store.rotations):
            self.rot_listbox.insert(tk.END, name)
        chars = sorted(self.store.characters.keys())
        self.hit_char_cb["values"] = chars
        self.ins_combo_char_cb["values"] = chars
        self.tb_template_cb["values"] = sorted(self.store.buff_templates.keys())
        contrib_vals = [""] + chars
        self.hit_contrib1_cb["values"] = contrib_vals
        self.hit_contrib2_cb["values"] = contrib_vals
        self.hit_contrib3_cb["values"] = contrib_vals

    def on_rotation_select(self, event=None):
        sel = self.rot_listbox.curselection()
        if not sel:
            return
        r = self.store.rotations[self.rot_listbox.get(sel[0])]
        self.rot_name.set(r.name)
        self.rot_duration.set(str(r.duration))
        self.rot_notes.set(r.notes)
        self._current_hits = deepcopy(r.hits)
        self._current_tbuffs = deepcopy(r.timed_buffs)
        self._reload_hits_tree()
        self._reload_tbuffs_tree()

    def new_rotation(self):
        self.rot_listbox.selection_clear(0, tk.END)
        self.rot_name.set("")
        self.rot_duration.set("20")
        self.rot_notes.set("")
        self._current_hits = []
        self._current_tbuffs = []
        self._reload_hits_tree()
        self._reload_tbuffs_tree()

    def save_rotation(self):
        name = self.rot_name.get().strip()
        if not name:
            messagebox.showwarning("Missing name", "Rotation name is required.")
            return
        try:
            r = Rotation(
                name=name,
                duration=float(self.rot_duration.get() or 20),
                hits=deepcopy(self._current_hits),
                timed_buffs=deepcopy(self._current_tbuffs),
                notes=self.rot_notes.get(),
            )
        except ValueError as e:
            messagebox.showerror("Invalid input", str(e))
            return
        old_val = deepcopy(self.store.rotations.get(name))
        self.store.rotations[name] = r
        self._push_store_dict_undo(
            "rotations", name, old_val, r,
            f"Save rotation '{name}'",
            on_change=lambda: (self.refresh_rotation_list(), self.refresh_calc_selectors()),
        )
        self.refresh_rotation_list()
        self.refresh_calc_selectors()
        self.status.set(f"Rotation '{name}' saved")

    def delete_rotation(self):
        sel = self.rot_listbox.curselection()
        if not sel:
            return
        name = self.rot_listbox.get(sel[0])
        if messagebox.askyesno("Delete", f"Delete rotation '{name}'?"):
            old_val = deepcopy(self.store.rotations[name])
            del self.store.rotations[name]
            self._push_store_dict_undo(
                "rotations", name, old_val, None,
                f"Delete rotation '{name}'",
                on_change=lambda: (self.refresh_rotation_list(), self.refresh_calc_selectors(),
                                   self.new_rotation()),
            )
            self.refresh_rotation_list()
            self.new_rotation()

    def _resolve_hit(self, hit: Hit) -> Optional[dict]:
        """Look up talent definition on the character and apply any overrides."""
        if hit.character not in self.store.characters:
            return None
        char = self.store.characters[hit.character]
        talent = char.get_talent(hit.talent_name)
        if talent is None:
            return None
        # Effective snapshot time: explicit on hit, or None (dynamic)
        snap_t = hit.snapshot_time
        uses_snapshot = talent.snapshots or (snap_t is not None)
        return {
            "display_name": hit.display_name,
            "multiplier": hit.multiplier_override if hit.multiplier_override is not None else talent.multiplier,
            "element": hit.element_override or talent.element,
            "talent_type": hit.talent_type_override or talent.talent_type,
            "scaling_stat": hit.scaling_override or talent.scaling_stat,
            "reaction": hit.reaction,
            "additive_base": hit.additive_base,
            "is_transformative": hit.is_transformative,
            "count": hit.count,
            "char_level": char.level,
            "snapshots": talent.snapshots,
            "uses_snapshot": uses_snapshot,
            "snapshot_time": snap_t,
        }

    def _hit_row_values(self, h: Hit) -> tuple:
        resolved = self._resolve_hit(h)
        ttype = resolved["talent_type"] if resolved else "?"
        element = resolved["element"] if resolved else "?"
        snap = ""
        if h.snapshot_time is not None:
            snap = f"{h.snapshot_time:.1f}"
        elif resolved and resolved.get("snapshots"):
            snap = "!"
        return (
            f"{h.time:.2f}", h.character, h.talent_name, ttype, element,
            h.reaction, snap, h.count,
        )

    def _reload_hits_tree(self):
        """Rebuild hits tree with combo groups as expandable parents."""
        self.hits_tree.delete(*self.hits_tree.get_children())
        self._hits_tree_map = {}
        # Work on index-stable list: keep _current_hits order but display sorted by time
        indexed = list(enumerate(self._current_hits))
        indexed.sort(key=lambda pair: pair[1].time)
        seen_groups: Dict[str, str] = {}  # group_id -> tree item id

        for idx, h in indexed:
            if h.combo_group:
                if h.combo_group not in seen_groups:
                    label = h.combo_label or "Combo"
                    n = sum(1 for x in self._current_hits if x.combo_group == h.combo_group)
                    parent = self.hits_tree.insert(
                        "", tk.END,
                        text="▾",
                        values=(
                            f"{h.time:.2f}", h.character, f"⟪ {label} ⟫",
                            f"{n} hits", "", "", "", "",
                        ),
                        tags=("combo_group",),
                        open=True,
                    )
                    seen_groups[h.combo_group] = parent
                    self._hits_tree_map[parent] = ("group", h.combo_group)
                parent = seen_groups[h.combo_group]
                iid = self.hits_tree.insert(
                    parent, tk.END, text="",
                    values=self._hit_row_values(h),
                    tags=("hit",),
                )
                self._hits_tree_map[iid] = ("hit", idx)
            else:
                iid = self.hits_tree.insert(
                    "", tk.END, text="",
                    values=self._hit_row_values(h),
                    tags=("hit",),
                )
                self._hits_tree_map[iid] = ("hit", idx)

        # Tint combo group rows for dark theme
        self.hits_tree.tag_configure(
            "combo_group",
            background=self.colors.get("bg3", "#33334a"),
            foreground=self.colors.get("accent", "#7aa2f7"),
        )

    def _reload_tbuffs_tree(self):
        self.tbuff_tree.delete(*self.tbuff_tree.get_children())
        for b in sorted(self._current_tbuffs, key=lambda x: x.start):
            self.tbuff_tree.insert("", tk.END, values=(b.template_name, f"{b.start:.2f}", f"{b.duration:.2f}"))

    def on_hit_char_changed(self, event=None):
        cname = self.hit_char.get()
        if cname not in self.store.characters:
            self.hit_talent_cb["values"] = []
            return
        char = self.store.characters[cname]
        self.hit_talent_cb["values"] = char.talent_names()

    def on_ins_combo_char_changed(self, event=None):
        cname = self.ins_combo_char.get()
        if cname not in self.store.characters:
            self.ins_combo_cb["values"] = []
            return
        char = self.store.characters[cname]
        self.ins_combo_cb["values"] = char.combo_names()
        if char.combo_names():
            self.ins_combo_name.set(char.combo_names()[0])

    def insert_combo(self):
        """Expand a character combo at the given start time and append the hits."""
        cname = self.ins_combo_char.get()
        combo_name = self.ins_combo_name.get()
        if not cname or cname not in self.store.characters:
            messagebox.showwarning("Select character", "Choose a character that has combos.")
            return
        if not combo_name:
            messagebox.showwarning("Select combo", "Choose a combo to insert.")
            return
        try:
            start = float(self.ins_combo_start.get() or 0)
        except ValueError:
            messagebox.showerror("Invalid", "Start time must be a number.")
            return
        char = self.store.characters[cname]
        new_hits = char.expand_combo(combo_name, start)
        if not new_hits:
            messagebox.showinfo("Empty", f"Combo '{combo_name}' produced no hits.")
            return
        group_id = uuid.uuid4().hex[:10]
        for h in new_hits:
            h.combo_group = group_id
            h.combo_label = f"{cname} · {combo_name}"
        self._push_hits_undo(f"Insert combo '{combo_name}'")
        self._current_hits.extend(new_hits)
        self._current_hits.sort(key=lambda h: h.time)
        self._commit_hits_undo()
        self._reload_hits_tree()
        self.status.set(f"Inserted combo '{combo_name}' ({len(new_hits)} hits) at t={start:.2f}s")

    def on_hit_select(self, event=None):
        sel = self.hits_tree.selection()
        if not sel:
            return
        item = sel[0]
        meta = self._hits_tree_map.get(item)
        if not meta or meta[0] == "group":
            # Selecting a combo group – don't fill the single-hit editor
            return
        idx = meta[1]
        if not (0 <= idx < len(self._current_hits)):
            return
        h = self._current_hits[idx]
        self.hit_time.set(str(h.time))
        self.hit_char.set(h.character)
        self.on_hit_char_changed()
        self.hit_talent_name.set(h.talent_name)
        self.hit_reaction.set(h.reaction)
        self.hit_count.set(str(h.count))
        self.hit_additive.set(str(h.additive_base))
        self.hit_transform.set(h.is_transformative)
        self.hit_snapshot_time.set("" if h.snapshot_time is None else str(h.snapshot_time))
        extras = list(h.extra_contributors or [])
        self.hit_contrib1.set(extras[0] if len(extras) > 0 else "")
        self.hit_contrib2.set(extras[1] if len(extras) > 1 else "")
        self.hit_contrib3.set(extras[2] if len(extras) > 2 else "")

    def _make_hit_from_form(self) -> Optional[Hit]:
        cname = self.hit_char.get()
        tname = self.hit_talent_name.get()
        if not cname or not tname:
            messagebox.showwarning("Missing", "Select a character and a talent.")
            return None
        if cname not in self.store.characters:
            messagebox.showwarning("Missing", f"Character '{cname}' not found.")
            return None
        if self.store.characters[cname].get_talent(tname) is None:
            messagebox.showwarning("Missing", f"Talent '{tname}' not defined on {cname}.")
            return None
        try:
            snap_raw = self.hit_snapshot_time.get().strip()
            snap_t = float(snap_raw) if snap_raw else None
            extras = []
            for var in (self.hit_contrib1, self.hit_contrib2, self.hit_contrib3):
                n = var.get().strip()
                if n and n != cname and n not in extras:
                    extras.append(n)
            return Hit(
                time=float(self.hit_time.get() or 0),
                character=cname,
                talent_name=tname,
                reaction=self.hit_reaction.get(),
                additive_base=float(self.hit_additive.get() or 0),
                is_transformative=self.hit_transform.get(),
                count=int(self.hit_count.get() or 1),
                snapshot_time=snap_t,
                extra_contributors=extras[:3],
            )
        except ValueError as e:
            messagebox.showerror("Invalid hit", str(e))
            return None

    def add_hit(self):
        h = self._make_hit_from_form()
        if h:
            self._push_hits_undo("Add hit")
            self._current_hits.append(h)
            self._commit_hits_undo()
            self._reload_hits_tree()

    def update_hit(self):
        sel = self.hits_tree.selection()
        if not sel:
            messagebox.showinfo("Select", "Select a hit to update.")
            return
        item = sel[0]
        meta = self._hits_tree_map.get(item)
        if not meta or meta[0] == "group":
            messagebox.showinfo("Combo group", "Select an individual hit under the group to update it.")
            return
        idx = meta[1]
        if not (0 <= idx < len(self._current_hits)):
            messagebox.showwarning("Stale", "Selection is out of date – try re-selecting the hit.")
            return
        new_h = self._make_hit_from_form()
        if not new_h:
            return
        # Preserve combo membership when updating a nested hit
        old = self._current_hits[idx]
        new_h.combo_group = old.combo_group
        new_h.combo_label = old.combo_label
        self._push_hits_undo("Update hit")
        self._current_hits[idx] = new_h
        self._commit_hits_undo()
        self._reload_hits_tree()

    def remove_hit(self):
        """Delete every selected hit and/or combo group (multi-select supported)."""
        sel = self.hits_tree.selection()
        if not sel:
            messagebox.showinfo("Select", "Select one or more hits / combo groups first.\n"
                                          "Tip: Ctrl+click or Shift+click to multi-select.")
            return

        groups_to_remove = set()
        indices_to_remove = set()
        stale = 0

        for item in sel:
            meta = self._hits_tree_map.get(item)
            if not meta:
                stale += 1
                continue
            kind, value = meta
            if kind == "group":
                groups_to_remove.add(value)
            elif kind == "hit":
                indices_to_remove.add(value)

        # If a group is selected, drop any child indices that belong to it
        # (they're already covered by the group delete).
        if groups_to_remove:
            for idx in list(indices_to_remove):
                if 0 <= idx < len(self._current_hits):
                    h = self._current_hits[idx]
                    if h.combo_group and h.combo_group in groups_to_remove:
                        indices_to_remove.discard(idx)

        if not groups_to_remove and not indices_to_remove:
            messagebox.showwarning(
                "Nothing to delete",
                "Selection could not be resolved. Re-select the rows and try again."
                + (f" ({stale} stale)" if stale else ""),
            )
            return

        self._push_hits_undo("Delete hit(s)/combo(s)")

        # Build the kept list in one pass so indices stay consistent
        remove_idx = set(indices_to_remove)
        new_hits = []
        deleted_hits = 0
        deleted_groups = 0
        for i, h in enumerate(self._current_hits):
            if h.combo_group and h.combo_group in groups_to_remove:
                deleted_hits += 1
                continue
            if i in remove_idx:
                deleted_hits += 1
                continue
            new_hits.append(h)
        deleted_groups = len(groups_to_remove)
        self._current_hits = new_hits

        self._commit_hits_undo()
        self._reload_hits_tree()

        parts = []
        if deleted_groups:
            parts.append(f"{deleted_groups} combo group(s)")
        if deleted_hits:
            parts.append(f"{deleted_hits} hit(s)")
        self.status.set("Deleted " + ", ".join(parts) if parts else "Nothing deleted")

    def add_timed_buff(self):
        name = self.tb_template.get()
        if not name or name not in self.store.buff_templates:
            messagebox.showwarning("Select template", "Choose a buff template first.")
            return
        try:
            tb = TimedBuff(
                template_name=name,
                start=float(self.tb_start.get() or 0),
                duration=float(self.tb_duration.get() or 10),
            )
        except ValueError as e:
            messagebox.showerror("Invalid", str(e))
            return
        self._push_hits_undo("Add timed buff")
        self._current_tbuffs.append(tb)
        self._commit_hits_undo()
        self._reload_tbuffs_tree()

    def remove_timed_buff(self):
        sel = self.tbuff_tree.selection()
        if not sel:
            return
        vals = self.tbuff_tree.item(sel[0], "values")
        name, start = vals[0], float(vals[1])
        self._push_hits_undo("Remove timed buff")
        self._current_tbuffs = [b for b in self._current_tbuffs
                                if not (b.template_name == name and abs(b.start - start) < 0.001)]
        self._commit_hits_undo()
        self._reload_tbuffs_tree()

    # =========================================================================
    # CALCULATOR TAB
    # =========================================================================
    def _build_calculator_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Calculator")

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=8, pady=8)
        ttk.Label(top, text="Rotation:", style="Header.TLabel").pack(side="left")
        self.calc_rotation = tk.StringVar()
        self.calc_rot_cb = ttk.Combobox(top, textvariable=self.calc_rotation, width=30, state="readonly")
        self.calc_rot_cb.pack(side="left", padx=6)
        self.calc_show_stats = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            top, text="Print full stats of involved characters",
            variable=self.calc_show_stats,
        ).pack(side="left", padx=10)
        ttk.Button(top, text="Run Calculation", style="Accent.TButton",
                   command=self.run_calculation).pack(side="left", padx=8)

        # Results
        results_frame = ttk.Frame(tab)
        results_frame.pack(fill="both", expand=True, padx=8, pady=4)
        self.calc_text = tk.Text(results_frame, wrap="none", font=("Consolas", 10),
                                 background="#fafbfd", relief="solid", borderwidth=1)
        scroll_y = ttk.Scrollbar(results_frame, orient="vertical", command=self.calc_text.yview)
        scroll_x = ttk.Scrollbar(results_frame, orient="horizontal", command=self.calc_text.xview)
        self.calc_text.configure(yscrollcommand=scroll_y.set, xscrollcommand=scroll_x.set)
        self.calc_text.pack(side="left", fill="both", expand=True)
        scroll_y.pack(side="right", fill="y")
        # horizontal scroll sits under the text area
        scroll_x.pack(side="bottom", fill="x")

    def refresh_calc_selectors(self):
        self.calc_rot_cb["values"] = sorted(self.store.rotations.keys())

    def _format_stats_block(self, name: str, stats: Stats) -> List[str]:
        """Pretty-print permanent stats for the calculator dump."""
        out = [f"  ┌─ {name}"]
        out.append(f"  │  ATK  base={stats.base_atk:.1f}  %={stats.atk_pct*100:.1f}%  flat={stats.flat_atk:.1f}"
                   f"  → total={stats.total_atk():.1f}")
        out.append(f"  │  HP   base={stats.base_hp:.1f}  %={stats.hp_pct*100:.1f}%  flat={stats.flat_hp:.1f}"
                   f"  → total={stats.total_hp():.1f}")
        out.append(f"  │  DEF  base={stats.base_def:.1f}  %={stats.def_pct*100:.1f}%  flat={stats.flat_def:.1f}"
                   f"  → total={stats.total_def():.1f}")
        out.append(f"  │  EM={stats.em:.1f}  ER={stats.er*100:.1f}%  "
                   f"CRIT Rate={stats.crit_rate*100:.1f}%  CRIT DMG={stats.crit_dmg*100:.1f}%")
        out.append(f"  │  All DMG%={stats.all_dmg_bonus*100:.1f}%  "
                   f"DEF shred={stats.def_reduction*100:.1f}%  DEF ignore={stats.def_ignore*100:.1f}%")
        if stats.dmg_bonus:
            dmg_bits = ", ".join(f"{k} {v*100:.1f}%" for k, v in sorted(stats.dmg_bonus.items()) if v)
            if dmg_bits:
                out.append(f"  │  Elemental DMG%: {dmg_bits}")
        if stats.res_shred:
            res_bits = ", ".join(f"{k} {v*100:.1f}%" for k, v in sorted(stats.res_shred.items()) if v)
            if res_bits:
                out.append(f"  │  RES shred: {res_bits}")
        if stats.reaction_bonus:
            rx_bits = ", ".join(f"{k} {v*100:.1f}%" for k, v in sorted(stats.reaction_bonus.items()) if v)
            if rx_bits:
                out.append(f"  │  Reaction bonus: {rx_bits}")
        out.append("  └─")
        return out

    def run_calculation(self):
        rname = self.calc_rotation.get()
        if not rname or rname not in self.store.rotations:
            messagebox.showwarning("Select rotation", "Choose a rotation to calculate.")
            return
        rotation = self.store.rotations[rname]
        enemy = self.store.enemy

        lines = []
        lines.append(f"Rotation: {rotation.name}  ({rotation.duration:.1f}s)")
        lines.append("=" * 100)

        # Optional full-stats dump for every character that appears in the rotation
        if self.calc_show_stats.get():
            involved = sorted({h.character for h in rotation.hits if h.character in self.store.characters})
            # Also include providers referenced by timed buffs
            for tb in rotation.timed_buffs:
                tmpl = self.store.buff_templates.get(tb.template_name)
                if tmpl and tmpl.provider_name and tmpl.provider_name in self.store.characters:
                    if tmpl.provider_name not in involved:
                        involved.append(tmpl.provider_name)
            lines.append("PERMANENT STATS (character + weapon + artifacts; no temporary buffs)")
            lines.append("-" * 100)
            if not involved:
                lines.append("  (no characters resolved in this rotation)")
            for cname in involved:
                s = self.store.get_character_full_stats(cname)
                lines.extend(self._format_stats_block(cname, s))
            lines.append("")
            lines.append("ENEMY")
            lines.append(f"  Level {enemy.level}  RES: " +
                         ", ".join(f"{k} {v*100:.0f}%" for k, v in sorted(enemy.res.items())))
            lines.append("=" * 100)
        lines.append(
            f"{'Time':>7}  {'Character':<12} {'Hit':<18} {'Type':<16} "
            f"{'Avg DMG':>11} {'Crit DMG':>11}  Active Buffs"
        )
        lines.append("-" * 100)

        total_avg = 0.0
        total_crit = 0.0
        per_char: Dict[str, float] = {}

        for hit in sorted(rotation.hits, key=lambda h: h.time):
            resolved = self._resolve_hit(hit)
            if resolved is None:
                lines.append(
                    f"[{hit.time:5.2f}s]  WARNING: cannot resolve "
                    f"'{hit.character}' / '{hit.talent_name}'"
                )
                continue

            base_stats = self.store.get_character_full_stats(hit.character)

            # Buff reference time: snapshot cast time, or hit time if dynamic
            buff_time = hit.time
            snap_note = ""
            if resolved["uses_snapshot"]:
                if resolved["snapshot_time"] is not None:
                    buff_time = resolved["snapshot_time"]
                    snap_note = f" [snap@{buff_time:.1f}s]"
                elif resolved["snapshots"]:
                    snap_note = " [SNAP talent but no snapshot_time – using hit time!]"

            # Collect active buffs at buff_time (+ talent-type filter)
            # Provider-scaled values use the provider's PERMANENT stats only.
            active_names = []
            buff_stats = Stats()
            buff_additive = 0.0
            for tb in rotation.timed_buffs:
                if tb.start <= buff_time < tb.start + tb.duration:
                    if tb.template_name in self.store.buff_templates:
                        tmpl = self.store.buff_templates[tb.template_name]
                        if tmpl.applies_to(resolved["talent_type"]):
                            part_stats, part_add = self.store.resolve_buff_template(tmpl)
                            buff_stats = buff_stats.apply(part_stats)
                            buff_additive += part_add
                            active_names.append(tb.template_name)

            final_stats = base_stats.apply(buff_stats)
            non, avg, crit = calculate_hit_damage(
                multiplier=resolved["multiplier"],
                element=resolved["element"],
                scaling_stat=resolved["scaling_stat"],
                reaction=resolved["reaction"],
                additive_base=resolved["additive_base"] + buff_additive,
                is_transformative=resolved["is_transformative"],
                count=resolved["count"],
                stats=final_stats,
                char_level=resolved["char_level"],
                enemy=enemy,
            )

            # Multi-contributor blend for pure Lunar-Charged / Lunar-Crystallize /
            # Stellar-Swirl reaction instances (Direct kit hits are NOT blended).
            contrib_note = ""
            is_pure_rxn = resolved["is_transformative"] or resolved["reaction"] in ALL_PURE_REACTION
            extras = [c for c in (hit.extra_contributors or []) if c and c in self.store.characters]
            if (
                is_pure_rxn
                and resolved["reaction"] in MULTI_CONTRIBUTOR_REACTIONS
                and extras
            ):
                dmg_element = reaction_damage_element(resolved["reaction"], resolved["element"])
                res = enemy.res.get(dmg_element, 0.10) - final_stats.res_shred.get(dmg_element, 0.0)
                res_mult = resistance_multiplier(res)
                r_key = _reaction_bonus_key(resolved["reaction"])
                # Personal expected damage for the main character (already computed avg/count)
                main_personal = avg / max(1, resolved["count"])
                personals = [main_personal]
                for cname in extras[:3]:
                    c_stats = self.store.get_character_full_stats(cname)
                    # Contributors use their permanent stats only (no timed buffs)
                    c_r_bonus = c_stats.reaction_bonus.get(r_key, 0.0)
                    _n, c_avg, _c = lunar_stellar_damage(
                        resolved["reaction"],
                        c_stats.em,
                        res_mult,
                        c_r_bonus,
                        can_crit=True,
                        crit_rate=c_stats.crit_rate,
                        crit_dmg=c_stats.crit_dmg,
                    )
                    personals.append(c_avg)
                blended = blend_contributor_damages(personals) * resolved["count"]
                # Scale crit proportionally to keep crit column meaningful
                if avg > 0:
                    crit = crit * (blended / avg)
                avg = blended
                contrib_note = f" [blend:{'+'.join([hit.character]+extras[:3])}]"

            total_avg += avg
            total_crit += crit
            per_char[hit.character] = per_char.get(hit.character, 0.0) + avg

            buff_str = ", ".join(active_names) if active_names else "-"
            lines.append(
                f"[{hit.time:5.2f}s]  {hit.character:<12} {resolved['display_name']:<18} "
                f"{resolved['talent_type']:<16} "
                f"{avg:11,.0f} {crit:11,.0f}  {buff_str}{snap_note}{contrib_note}"
            )

        lines.append("-" * 100)
        dps = total_avg / rotation.duration if rotation.duration > 0 else 0
        lines.append(f"Total Average Damage : {total_avg:,.0f}")
        lines.append(f"Total Crit Damage    : {total_crit:,.0f}")
        lines.append(f"Team DPS (average)   : {dps:,.0f}")
        lines.append("")
        lines.append("Per Character:")
        for name, dmg in sorted(per_char.items(), key=lambda x: -x[1]):
            pct = dmg / total_avg * 100 if total_avg else 0
            lines.append(f"  {name:<12}: {dmg:12,.0f}  ({pct:5.1f}%)")
        lines.append("=" * 90)

        self.calc_text.delete("1.0", tk.END)
        self.calc_text.insert("1.0", "\n".join(lines))
        self.status.set(f"Calculated '{rname}' – DPS {dps:,.0f}")

    # =========================================================================
    # ENEMY TAB
    # =========================================================================
    def _build_enemy_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Enemy")

        frame = ttk.LabelFrame(tab, text="Enemy Settings")
        frame.pack(padx=20, pady=20, anchor="nw")

        self.enemy_level = tk.StringVar(value=str(self.store.enemy.level))
        ttk.Label(frame, text="Level").grid(row=0, column=0, sticky="w", padx=6, pady=4)
        ttk.Entry(frame, textvariable=self.enemy_level, width=8).grid(row=0, column=1, sticky="w", padx=6)

        self.enemy_res_vars: Dict[str, tk.StringVar] = {}
        ttk.Label(frame, text="Base Resistance").grid(row=1, column=0, columnspan=2, sticky="w", padx=6, pady=(10, 2))
        for i, el in enumerate(["Physical", "Pyro", "Hydro", "Electro", "Cryo", "Anemo", "Geo", "Dendro"]):
            ttk.Label(frame, text=el).grid(row=2+i, column=0, sticky="w", padx=6)
            v = tk.StringVar(value=str(self.store.enemy.res.get(el, 0.10)))
            ttk.Entry(frame, textvariable=v, width=8).grid(row=2+i, column=1, sticky="w", padx=6)
            self.enemy_res_vars[el] = v

        ttk.Button(frame, text="Save Enemy Settings", command=self.save_enemy).grid(
            row=12, column=0, columnspan=2, pady=12)

    def save_enemy(self):
        try:
            level = int(self.enemy_level.get() or 90)
            res = {}
            for el, var in self.enemy_res_vars.items():
                res[el] = float(var.get() or 0.10)
            self.store.enemy = Enemy(level=level, res=res)
            self.status.set("Enemy settings updated (remember to File → Save)")
        except ValueError as e:
            messagebox.showerror("Invalid", str(e))


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    app = GenshinDPSApp()
    app.mainloop()