import Std
open Std

namespace Cascade

/--
We work abstractly over a type `C` of candidates (e.g., complex numbers),
a predicate `zero : C → Prop` selecting zeros, and `onCritical : C → Prop`.

`offCritical z` means `z` is a zero and not on the critical line.

Two hypotheses mirror the Coq version (we pass them as parameters to the theorems):
* `cascadeMany`: from one off-critical zero, obtain arbitrarily many pairwise distinct off-critical zeros
* `densityFinite`: there is a uniform finite bound on the number of distinct off-critical zeros

From these we derive that no off-critical zeros exist, and as a corollary,
all zeros lie on the critical line.
-/

def offCritical {C : Type} (zero : C → Prop) (onCritical : C → Prop) (z : C) : Prop :=
  zero z ∧ ¬ onCritical z

/-- Cascade theorem: under the two hypotheses, no off-critical zeros exist. -/
theorem cascadeTheorem
  {C : Type}
  (zero : C → Prop) (onCritical : C → Prop)
  (cascadeMany :
    (∃ z, offCritical zero onCritical z) →
    ∀ n : Nat, ∃ l : List C,
      (∀ z ∈ l, offCritical zero onCritical z) ∧ l.Nodup ∧ l.length = Nat.succ n)
  (densityFinite :
    ∃ N : Nat, ∀ l : List C,
      (∀ z ∈ l, offCritical zero onCritical z) → l.Nodup → l.length ≤ N)
  : ¬ (∃ z, offCritical zero onCritical z) := by
  intro Hex
  rcases densityFinite with ⟨N, hN⟩
  rcases cascadeMany Hex N with ⟨l, hlAll, hlNd, hlLen⟩
  have hle : l.length ≤ N := hN l hlAll hlNd
  have hcontr : Nat.succ N ≤ N := by simpa [hlLen] using hle
  exact (Nat.not_succ_le_self N) hcontr

/-- Classical corollary: all zeros lie on the critical line. -/
theorem allZerosOnCritical
  {C : Type}
  (zero : C → Prop) (onCritical : C → Prop)
  (cascadeMany :
    (∃ z, offCritical zero onCritical z) →
    ∀ n : Nat, ∃ l : List C,
      (∀ z ∈ l, offCritical zero onCritical z) ∧ l.Nodup ∧ l.length = Nat.succ n)
  (densityFinite :
    ∃ N : Nat, ∀ l : List C,
      (∀ z ∈ l, offCritical zero onCritical z) → l.Nodup → l.length ≤ N)
  : ∀ z, zero z → onCritical z := by
  intro z hz
  classical
  by_cases h : onCritical z
  · exact h
  ·
    have Hex : ∃ z, offCritical zero onCritical z := ⟨z, ⟨hz, h⟩⟩
    exact False.elim ((cascadeTheorem zero onCritical cascadeMany densityFinite) Hex)

/-! A tiny specialization to ensure the generic theorem is usable. -/
namespace Toy
  inductive Point | a | b | c deriving DecidableEq
  open Point

  def zero (_ : Point) : Prop := True
  def onCritical : Point → Prop
    | a => True
    | _ => False
  def offc (p : Point) : Prop := zero p ∧ ¬ onCritical p

  axiom axCascadeMany :
    (∃ z, offc z) → ∀ n, ∃ l : List Point,
      (∀ z ∈ l, offc z) ∧ l.Nodup ∧ l.length = Nat.succ n

  axiom axDensityFinite :
    ∃ N, ∀ l : List Point,
      (∀ z ∈ l, offc z) → l.Nodup → l.length ≤ N

  theorem noOffCritical : ¬ (∃ z, offc z) := by
    simpa [offc] using
      (Cascade.cascadeTheorem (C:=Point) zero onCritical axCascadeMany axDensityFinite)

  theorem allOnCritical : ∀ z, zero z → onCritical z := by
    intro z hz
    have h := Cascade.allZerosOnCritical (C:=Point) zero onCritical axCascadeMany axDensityFinite
    exact h z hz

end Toy

end Cascade
