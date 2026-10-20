module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith

/-!
# Elementary matching results for Erdős problem 710

Source: https://www.erdosproblems.com/710 .
This development gives Hall equivalence and elementary bounds for distinct
multiples in the strict interval $(n,n+h)$. It does not prove an asymptotic
formula and makes no claim to solve Erdős problem 710.
-/

public section

namespace Erdos710

/-- The strict interval `(n,n+h)` contains pairwise distinct multiples
of every index `1, ..., n`. -/
def HasMatching (n h : ℕ) : Prop :=
  ∃ a : Fin n → ℕ,
    Function.Injective a ∧
      ∀ i : Fin n, n < a i ∧ a i < n + h ∧ (i.val + 1) ∣ a i

/-- The finite set of admissible right-hand neighbors of index `i`. -/
def neighbors (n h : ℕ) (i : Fin n) : Finset ℕ :=
  (Finset.Ioo n (n + h)).filter (fun m => (i.val + 1) ∣ m)

/-- Hall's necessary cardinality condition for the divisibility graph. -/
def HallCondition (n h : ℕ) : Prop :=
  ∀ S : Finset (Fin n),
    S.card ≤ (S.biUnion (neighbors n h)).card

/-- An actual matching always satisfies Hall's neighborhood condition. -/
theorem hasMatching_implies_hall (n h : ℕ)
    (hm : HasMatching n h) : HallCondition n h := by
  classical
  obtain ⟨a, ha_inj, ha⟩ := hm
  intro S
  have hsub : S.image a ⊆ S.biUnion (neighbors n h) := by
    intro x hx
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hiS, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioo.mpr ⟨(ha i).1, (ha i).2.1⟩, (ha i).2.2⟩
  calc
    S.card = (S.image a).card := (Finset.card_image_of_injective S ha_inj).symm
    _ ≤ (S.biUnion (neighbors n h)).card := Finset.card_le_card hsub

/-- Hall's condition is also sufficient. This is the exact finite
matching reduction, via Mathlib's finite Hall marriage theorem.

The key number-theoretic obstruction in Erdős #710 is to establish Hall's
inequalities at a sharp asymptotic window length. -/
theorem hall_iff_hasMatching (n h : ℕ) :
    HallCondition n h ↔ HasMatching n h := by
  classical
  constructor
  · intro hh
    have hh' : ∀ S : Finset (Fin n),
        S.card ≤ (S.biUnion (neighbors n h)).card := hh
    obtain ⟨a, ha_inj, ha⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective'
        (neighbors n h)).mp hh'
    refine ⟨a, ha_inj, ?_⟩
    intro i
    have hi := Finset.mem_filter.mp (ha i)
    have hinterval := Finset.mem_Ioo.mp hi.1
    exact ⟨hinterval.1, hinterval.2, hi.2⟩
  · exact hasMatching_implies_hall n h

/-- Finite failures of Hall are exactly the obstructions to a matching. -/
theorem not_matching_iff_hall_failure (n h : ℕ) :
    (¬ HasMatching n h) ↔
      ∃ S : Finset (Fin n),
        (S.biUnion (neighbors n h)).card < S.card := by
  classical
  constructor
  · intro h
    have hn : ¬ HallCondition n h := by
      intro hh
      exact hnot ((hall_iff_hasMatching n h).mp hh)
    unfold HallCondition at hn
    push Not at hn
    exact hn
  · rintro ⟨S, hS⟩ hm
    have h := (hasMatching_implies_hall n h hm) S
    omega

/-- Lengthening the interval cannot destroy an existing matching. -/
theorem hasMatching_mono (n : ℕ) {h H : ℕ}
    (hh : h ≤ H) (hm : HasMatching n h) : HasMatching n H := by
  rcases hm with ⟨a, ha_inj, ha⟩
  refine ⟨a, ha_inj, ?_⟩
  intro i
  rcases ha i with ⟨hl, hu, hdvd⟩
  exact ⟨hl, by omega, hdvd⟩

/-- A fully explicit matching gives the coarse upper bound `f(n) ≤ n²+1`.
Use `a_i = (i+1)(n+1)` with zero-based Lean indices. -/
theorem hasMatching_quadratic (n : ℕ) : HasMatching n (n * n + 1) := by
  refine ⟨(fun i : Fin n => (i.val + 1) * (n + 1)), ?_, ?_⟩
  · intro i j hij
    have hc : i.val + 1 = j.val + 1 :=
      Nat.eq_of_mul_eq_mul_right (by omega : 0 < n + 1) hij
    exact Fin.ext (by omega)
  · intro i
    have hi0 : 1 ≤ i.val + 1 := by omega
    have hiN : i.val + 1 ≤ n := by omega
    have hlo : n + 1 ≤ (i.val + 1) * (n + 1) := by
      calc
        n + 1 = 1 * (n + 1) := by omega
        _ ≤ (i.val + 1) * (n + 1) :=
          Nat.mul_le_mul_right (n + 1) hi0
    have hhi : (i.val + 1) * (n + 1) ≤ n * (n + 1) :=
      Nat.mul_le_mul_right (n + 1) hiN
    refine ⟨by omega, ?_, ⟨n + 1, rfl⟩⟩
    nlinarith

private theorem matching_exists (n : ℕ) : ∃ h : ℕ, HasMatching n h :=
  ⟨n * n + 1, hasMatching_quadratic n⟩

/-- Exactly the least permissible length in the source's open-interval
convention. -/
noncomputable def f (n : ℕ) : ℕ := by
  classical
  exact Nat.find (matching_exists n)

/-- The least permissible length actually admits a matching. -/
theorem f_spec (n : ℕ) : HasMatching n (f n) := by
  classical
  unfold f
  exact Nat.find_spec (matching_exists n)

/-- The least permissible length is no larger than any valid length. -/
theorem f_minimal (n h : ℕ) (hh : HasMatching n h) : f n ≤ h := by
  classical
  unfold f
  exact Nat.find_min' (matching_exists n) hh

/-- Elementary quadratic upper bound; far weaker than Erdős--Pomerance. -/
theorem f_le_quadratic (n : ℕ) : f n ≤ n * n + 1 :=
  f_minimal n (n * n + 1) (hasMatching_quadratic n)

/-- The open interval of length h has only h-1 available integers;
therefore at least n+1 units of length are needed for n positive indices. -/
theorem hasMatching_lower (n h : ℕ) (hn : 0 < n)
    (hm : HasMatching n h) : n + 1 ≤ h := by
  rcases hm with ⟨a, ha_inj, ha⟩
  let b : Fin n → Fin (h - 1) := fun i =>
    ⟨a i - (n + 1), by
      have hb := ha i
      omega⟩
  have hb_inj : Function.Injective b := by
    intro i j hij
    apply ha_inj
    have hdiff := congrArg (fun z : Fin (h - 1) => z.val) hij
    change a i - (n + 1) = a j - (n + 1) at hdiff
    have hi := ha i
    have hj := ha j
    omega
  have hcard : n ≤ h - 1 := by
    simpa using (Fintype.card_le_of_injective b hb_inj)
  omega

/-- Elementary lower bound from the pigeonhole principle. -/
theorem f_ge_linear (n : ℕ) (hn : 0 < n) : n + 1 ≤ f n :=
  hasMatching_lower n (f n) hn (f_spec n)

/-- Exact smallest length for the one-divisor instance. -/
theorem f_one : f 1 = 2 := by
  have hlo := f_ge_linear 1 (by omega)
  have hhi := f_le_quadratic 1
  omega


end Erdos710
