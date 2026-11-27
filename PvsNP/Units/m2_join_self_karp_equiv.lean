import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_join_karp_sides

/-
Uses the settled units PvsNP/Units/fr_ladner.lean and
PvsNP/Units/m2_join_karp_sides.lean of github.com/makedotfun/pvsnp
(Apache License 2.0): the `cpt_*` polytime combinators (`cpt_tail`,
`cpt_const`, `cpt_sel`, `cpt_ifEmpty` from
`PEqualNP.Library.Universal`; `cpt_comp`, `cpt_pair`, `cpt_id` from
`PEqualNP.Library.Machines`) and the fact that each side of a join
reduces to the join. All names are fully qualified: `cpt_comp` /
`cpt_pair` / `cpt_id` live in `Machines`, not `Universal`.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_join_self_karp_equiv

/-- The flag `[true]` iff the input is empty, polynomial-time. -/
theorem flag_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => if x = [] then [true] else []) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const [true]))
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_ifEmpty

/-- Strip the head bit, sending `[]` to the fixed string `z`:
`sel` picks the second branch exactly when the flag is nonempty,
i.e. exactly when the input is empty. -/
theorem strip_poly (z : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool =>
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.sel
          (if x = [] then [true] else []) x.tail z) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_sel flag_poly
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const z)

end PvsNP.Units.m2_join_self_karp_equiv

/-- A language missing some string and its join with itself reduce to each other (TM2):
`L` reduces to the join by writing `false` in front (settled `m2_join_karp_sides`),
and the join reduces to `L` by stripping the head bit, sending `[]` to the missing
string `z` (which is outside `L`, matching `[]` being outside the join). -/
theorem PvsNP.Units.m2_join_self_karp_equiv :
    ∀ L : Language Bool, (∃ z : List Bool, z ∉ L) →
      PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ L, x = true :: y)} : Language Bool) L ∧
        PvsNP.KarpReducible L ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ L, x = true :: y)} : Language Bool) := by
  intro L ⟨z, hz⟩
  refine ⟨⟨fun x : List Bool =>
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.sel
      (if x = [] then [true] else []) x.tail z,
    PvsNP.Units.m2_join_self_karp_equiv.strip_poly z, fun x => ?_⟩,
    (PvsNP.Units.m2_join_karp_sides L L).1⟩
  cases x with
  | nil => simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.sel, hz]
  | cons b y =>
    cases b with
    | false => simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.sel]
    | true => simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.sel]
