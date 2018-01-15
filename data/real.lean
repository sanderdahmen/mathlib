/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

The (classical) real numbers ℝ. This is a direct construction
from Cauchy sequences.
-/
import data.rat algebra.ordered_field algebra.big_operators

theorem exists_forall_ge_and {α} [linear_order α] {P Q : α → Prop} :
  (∃ i, ∀ j ≥ i, P j) → (∃ i, ∀ j ≥ i, Q j) →
  ∃ i, ∀ j ≥ i, P j ∧ Q j
| ⟨a, h₁⟩ ⟨b, h₂⟩ := let ⟨c, ac, bc⟩ := exists_ge_of_linear a b in
  ⟨c, λ j hj, ⟨h₁ _ (le_trans ac hj), h₂ _ (le_trans bc hj)⟩⟩

namespace rat
def cau_seq := {f : ℕ → ℚ // ∀ ε > 0, ∃ i, ∀ j ≥ i, abs (f j - f i) < ε }

instance : has_coe_to_fun cau_seq := ⟨_, subtype.val⟩

namespace cau_seq

theorem ext {f g : cau_seq} (h : ∀ i, f i = g i) : f = g :=
subtype.eq (funext h)

theorem cauchy (f : cau_seq) :
  ∀ {ε}, ε > 0 → ∃ i, ∀ j ≥ i, abs (f j - f i) < ε := f.2

theorem cauchy₂ (f : cau_seq) {ε:ℚ} (ε0 : ε > 0) :
  ∃ i, ∀ j k ≥ i, abs (f j - f k) < ε :=
begin
  refine exists_imp_exists (λ i hi j k ij ik, _) (f.cauchy (half_pos ε0)),
  rw ← add_halves ε,
  refine lt_of_le_of_lt (abs_sub_le _ _ _) (add_lt_add (hi _ ij) _),
  rw abs_sub, exact hi _ ik
end

theorem cauchy₃ (f : cau_seq) {ε:ℚ} (ε0 : ε > 0) :
  ∃ i, ∀ j ≥ i, ∀ k ≥ j, abs (f k - f j) < ε :=
let ⟨i, H⟩ := f.cauchy₂ ε0 in ⟨i, λ j ij k jk, H _ _ (le_trans ij jk) ij⟩

theorem bounded (f : cau_seq) : ∃ r, ∀ i, abs (f i) < r :=
begin
  cases f.cauchy zero_lt_one with i h,
  let R := (finset.range (i+1)).sum (λ j, abs (f j)),
  have : ∀ j ≤ i, abs (f j) ≤ R,
  { intros j ij, change (λ j, abs (f j)) j ≤ R,
    apply finset.single_le_sum,
    { intros, apply abs_nonneg },
    { rwa [finset.mem_range, nat.lt_succ_iff] } },
  refine ⟨R + 1, λ j, _⟩,
  cases lt_or_le j i with ij ij,
  { exact lt_of_le_of_lt (this _ (le_of_lt ij)) (lt_add_one _) },
  { have := lt_of_le_of_lt (abs_add _ _)
      (add_lt_add_of_le_of_lt (this _ (le_refl _)) (h _ ij)),
    rw [add_sub, add_comm] at this, simpa }
end

theorem bounded' (f : cau_seq) (x : ℚ) : ∃ r > x, ∀ i, abs (f i) < r :=
let ⟨r, h⟩ := f.bounded in
⟨max r (x+1), lt_of_lt_of_le (lt_add_one _) (le_max_right _ _),
  λ i, lt_of_lt_of_le (h i) (le_max_left _ _)⟩

def of_eq (f : cau_seq) (g : ℕ → ℚ) (e : ∀ i, f i = g i) : cau_seq :=
⟨g, λ ε, by rw [show g = f, from (funext e).symm]; exact f.cauchy⟩

instance : has_add cau_seq :=
⟨λ f g, ⟨λ i, f i + g i, λ ε ε0, begin
  refine exists_imp_exists (λ i H j ij, _)
    (exists_forall_ge_and (f.cauchy₃ $ half_pos ε0) (g.cauchy₃ $ half_pos ε0)),
  cases H _ (le_refl _) with H₁ H₂,
  simpa [add_halves ε] using
    lt_of_le_of_lt (abs_add _ _) (add_lt_add (H₁ _ ij) (H₂ _ ij))
end⟩⟩

@[simp] theorem add_apply (f g : cau_seq) (i : ℕ) : (f + g) i = f i + g i := rfl

instance : has_mul cau_seq :=
⟨λ f g, ⟨λ i, f i * g i, λ ε ε0, begin
  rcases f.bounded' 0 with ⟨F, F0, hF⟩,
  have εF0 := div_pos (half_pos ε0) F0,
  rcases g.bounded' 0 with ⟨G, G0, hG⟩,
  have εG0 := div_pos (half_pos ε0) G0,
  refine exists_imp_exists (λ i H j ij, _)
    (exists_forall_ge_and (f.cauchy₃ εG0) (g.cauchy₃ εF0)),
  cases H _ (le_refl _) with H₁ H₂,
  have := add_lt_add
    (mul_lt_mul' (le_of_lt $ H₁ _ ij) (hG i) (abs_nonneg _) εG0)
    (mul_lt_mul' (le_of_lt $ H₂ _ ij) (hF j) (abs_nonneg _) εF0),
  rw [← abs_mul, div_mul_cancel _ (ne_of_gt G0),
      ← abs_mul, div_mul_cancel _ (ne_of_gt F0), add_halves] at this,
  simpa [mul_add, mul_comm] using lt_of_le_of_lt (abs_add _ _) this
end⟩⟩

@[simp] theorem mul_apply (f g : cau_seq) (i : ℕ) : (f * g) i = f i * g i := rfl

def of_rat (x : ℚ) : cau_seq :=
⟨λ i, x, λ ε ε0, ⟨0, λ j ij, by simpa using ε0⟩⟩

@[simp] theorem of_rat_apply (x : ℚ) (i) : of_rat x i = x := rfl

instance : has_zero cau_seq := ⟨of_rat 0⟩
instance : has_one cau_seq := ⟨of_rat 1⟩

@[simp] theorem zero_apply (i) : (0 : cau_seq) i = 0 := rfl
@[simp] theorem one_apply (i) : (1 : cau_seq) i = 1 := rfl

theorem of_rat_add (x y : ℚ) : of_rat (x + y) = of_rat x + of_rat y :=
ext $ λ i, rfl

theorem of_rat_mul (x y : ℚ) : of_rat (x * y) = of_rat x * of_rat y :=
ext $ λ i, rfl

instance : has_neg cau_seq :=
⟨λ f, of_eq (of_rat (-1) * f) (λ x, -f x) (λ i, by simp)⟩

@[simp] theorem neg_apply (f : cau_seq) (i) : (-f) i = -f i := rfl

theorem of_rat_neg (x : ℚ) : of_rat (-x) = -of_rat x :=
ext $ λ i, rfl

instance : comm_ring cau_seq :=
by refine {neg := has_neg.neg, add := (+), zero := 0, mul := (*), one := 1, ..};
   { intros, apply ext, simp [mul_left_comm, mul_comm, mul_add] }

theorem of_rat_sub (x y : ℚ) : of_rat (x - y) = of_rat x - of_rat y :=
by rw [sub_eq_add_neg, of_rat_add, of_rat_neg]; refl

@[simp] theorem sub_apply (f g : cau_seq) (i : ℕ) : (f - g) i = f i - g i := rfl

def lim_zero (f : cau_seq) := ∀ ε > 0, ∃ i, ∀ j ≥ i, abs (f j) < ε

theorem add_lim_zero {f g} (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f + g)
| ε ε0 := begin
  refine exists_imp_exists (λ i H j ij, _)
    (exists_forall_ge_and (hf _ $ half_pos ε0) (hg _ $ half_pos ε0)),
  cases H _ ij with H₁ H₂,
  simpa [add_halves ε] using lt_of_le_of_lt (abs_add _ _) (add_lt_add H₁ H₂)
end

theorem mul_lim_zero (f) {g} (hg : lim_zero g) : lim_zero (f * g)
| ε ε0 := begin
  rcases f.bounded' 0 with ⟨F, F0, hF⟩,
  refine exists_imp_exists (λ i H j ij, _) (hg _ $ div_pos ε0 F0),
  have := mul_lt_mul' (le_of_lt $ hF j) (H _ ij) (abs_nonneg _) F0,
  rwa [mul_comm F, div_mul_cancel _ (ne_of_gt F0), ← abs_mul] at this
end

theorem neg_lim_zero {f} (hf : lim_zero f) : lim_zero (-f) :=
by rw ← neg_one_mul; exact mul_lim_zero _ hf

theorem sub_lim_zero {f g} (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f - g) :=
add_lim_zero hf (neg_lim_zero hg)

theorem zero_lim_zero : lim_zero 0
| ε ε0 := ⟨0, λ j ij, by simpa using ε0⟩

theorem of_rat_lim_zero {x : ℚ} : lim_zero (of_rat x) ↔ x = 0 :=
⟨λ H, abs_eq_zero.1 $
  eq_of_le_of_forall_le_of_dense (abs_nonneg _) $
  λ ε ε0, let ⟨i, hi⟩ := H _ ε0 in le_of_lt $ hi _ (le_refl _),
λ e, e.symm ▸ zero_lim_zero⟩

instance equiv : setoid cau_seq :=
⟨λ f g, lim_zero (f - g),
⟨λ f, by simp [zero_lim_zero],
 λ f g h, by simpa using neg_lim_zero h,
 λ f g h fg gh, by simpa using add_lim_zero fg gh⟩⟩

theorem lim_zero_congr {f g} (h : f ≈ g) : lim_zero f ↔ lim_zero g :=
⟨λ l, by simpa using add_lim_zero (setoid.symm h) l,
 λ l, by simpa using add_lim_zero h l⟩

theorem abs_pos_of_not_lim_zero {f} (hf : ¬ lim_zero f) :
  ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ abs (f j) :=
begin
  have := classical.prop_decidable,
  by_contra nk,
  refine hf (λ ε ε0, _),
  simp [not_forall] at nk,
  cases f.cauchy₃ (half_pos ε0) with i hi,
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩,
  refine ⟨j, λ k jk, _⟩,
  have := lt_of_le_of_lt (abs_add _ _) (add_lt_add (hi j ij k jk) hj),
  rwa [sub_add_cancel, add_halves] at this
end

theorem inv_aux {f} (hf : ¬ lim_zero f) :
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abs ((f j)⁻¹ - (f i)⁻¹) < ε :=
begin
  rcases abs_pos_of_not_lim_zero hf with ⟨K, K0, HK⟩,
  refine λ ε ε0, exists_imp_exists (λ i H j ij, _)
    (exists_forall_ge_and HK (f.cauchy₃ (mul_pos ε0 $ mul_pos K0 K0))),
  cases H _ (le_refl _) with iK H',
  replace H' := H' _ ij, have jK := (H _ ij).1,
  have i0 := lt_of_lt_of_le K0 iK,
  have j0 := lt_of_lt_of_le K0 jK,
  have KK := mul_pos K0 K0,
  rw [inv_sub_inv (abs_pos_iff.1 j0) (abs_pos_iff.1 i0),
      abs_div, abs_mul, mul_comm, abs_sub,
      ← mul_div_cancel ε (ne_of_gt KK)],
  exact div_lt_div H'
    (mul_le_mul iK jK (le_of_lt K0) (abs_nonneg _))
    (le_of_lt $ mul_pos ε0 KK) KK
end

def inv (f) (hf : ¬ lim_zero f) : cau_seq := ⟨_, inv_aux hf⟩

@[simp] theorem inv_apply {f} (hf i) : inv f hf i = (f i)⁻¹ := rfl

theorem inv_mul_cancel {f} (hf) : inv f hf * f ≈ 1 :=
λ ε ε0, let ⟨K, K0, i, H⟩ := abs_pos_of_not_lim_zero hf in
⟨i, λ j ij,
  by simpa [abs_pos_iff.1 (lt_of_lt_of_le K0 (H _ ij))] using ε0⟩

def pos (f : cau_seq) : Prop := ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j

theorem not_lim_zero_of_pos {f} : pos f → ¬ lim_zero f
| ⟨F, F0, hF⟩ H :=
  let ⟨i, h⟩ := exists_forall_ge_and hF (H _ F0),
      ⟨h₁, h₂⟩ := h _ (le_refl _) in
  not_lt_of_le h₁ (abs_lt.1 h₂).2

theorem of_rat_pos {x : ℚ} : pos (of_rat x) ↔ 0 < x :=
⟨λ ⟨K, K0, i, h⟩, lt_of_lt_of_le K0 (h _ (le_refl _)),
 λ h, ⟨x, h, 0, λ j _, le_refl _⟩⟩

theorem add_pos {f g} : pos f → pos g → pos (f + g)
| ⟨F, F0, hF⟩ ⟨G, G0, hG⟩ :=
  let ⟨i, h⟩ := exists_forall_ge_and hF hG in
  ⟨_, _root_.add_pos F0 G0, i,
    λ j ij, let ⟨h₁, h₂⟩ := h _ ij in add_le_add h₁ h₂⟩

theorem pos_add_lim_zero {f g} : pos f → lim_zero g → pos (f + g)
| ⟨F, F0, hF⟩ H :=
  let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0)) in
  ⟨_, half_pos F0, i, λ j ij, begin
    cases h j ij with h₁ h₂,
    have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1),
    rwa [← sub_eq_add_neg, sub_self_div_two] at this
  end⟩

theorem mul_pos {f g} : pos f → pos g → pos (f * g)
| ⟨F, F0, hF⟩ ⟨G, G0, hG⟩ :=
  let ⟨i, h⟩ := exists_forall_ge_and hF hG in
  ⟨_, _root_.mul_pos F0 G0, i,
    λ j ij, let ⟨h₁, h₂⟩ := h _ ij in
    mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩

theorem trichotomy (f) : pos f ∨ lim_zero f ∨ pos (-f) :=
begin
  cases classical.em (lim_zero f); simp *,
  rcases abs_pos_of_not_lim_zero h with ⟨K, K0, hK⟩,
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩,
  refine (le_total 0 (f i)).imp _ _;
    refine (λ h, ⟨K, K0, i, λ j ij, _⟩);
    have := (hi _ ij).1;
    cases hi _ (le_refl _) with h₁ h₂,
  { rwa abs_of_nonneg at this,
    rw abs_of_nonneg h at h₁,
    exact (le_add_iff_nonneg_right _).1
      (le_trans h₁ $ neg_le_sub_iff_le_add_left.1 $
        le_of_lt (abs_lt.1 $ h₂ _ ij).1) },
  { rwa abs_of_nonpos at this,
    rw abs_of_nonpos h at h₁,
    rw [← sub_le_sub_iff_right, zero_sub],
    exact le_trans (le_of_lt (abs_lt.1 $ h₂ _ ij).2) h₁ }
end

instance : has_lt cau_seq := ⟨λ f g, pos (g - f)⟩
instance : has_le cau_seq := ⟨λ f g, f < g ∨ f ≈ g⟩

theorem lt_of_lt_of_eq {f g h : cau_seq}
  (fg : f < g) (gh : g ≈ h) : f < h :=
by simpa using pos_add_lim_zero fg (neg_lim_zero gh)

theorem lt_of_eq_of_lt {f g h : cau_seq}
  (fg : f ≈ g) (gh : g < h) : f < h :=
by have := pos_add_lim_zero gh (neg_lim_zero fg);
   rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

theorem lt_trans {f g h : cau_seq} (fg : f < g) (gh : g < h) : f < h :=
by simpa using add_pos fg gh

theorem lt_irrefl {f : cau_seq} : ¬ f < f
| h := not_lim_zero_of_pos h (by simp [zero_lim_zero])

instance : preorder cau_seq :=
{ lt := (<),
  le := λ f g, f < g ∨ f ≈ g,
  le_refl := λ f, or.inr (setoid.refl _),
  le_trans := λ f g h fg, match fg with
    | or.inl fg, or.inl gh := or.inl $ lt_trans fg gh
    | or.inl fg, or.inr gh := or.inl $ lt_of_lt_of_eq fg gh
    | or.inr fg, or.inl gh := or.inl $ lt_of_eq_of_lt fg gh
    | or.inr fg, or.inr gh := or.inr $ setoid.trans fg gh
    end,
  lt_iff_le_not_le := λ f g,
    ⟨λ h, ⟨or.inl h,
      not_or (mt (lt_trans h) lt_irrefl) (not_lim_zero_of_pos h)⟩,
    λ ⟨h₁, h₂⟩, h₁.resolve_right
      (mt (λ h, or.inr (setoid.symm h)) h₂)⟩ }

theorem le_antisymm {f g : cau_seq} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
fg.resolve_left (not_lt_of_le gf)

theorem le_total (f g : cau_seq) : f ≤ g ∨ g ≤ f :=
begin
  rcases trichotomy (f - g) with h|h|h,
  { exact or.inr (or.inl h) },
  { exact or.inl (or.inr h) },
  { rw neg_sub at h, exact or.inl (or.inl h) }
end

end cau_seq

end rat

namespace NEW

def real := quotient rat.cau_seq.equiv
notation `ℝ` := real

namespace real
open rat rat.cau_seq

def mk : cau_seq → ℝ := quotient.mk

@[simp] theorem mk_eq_mk (f) : @eq ℝ ⟦f⟧ (mk f) := rfl

theorem mk_eq {f g} : mk f = mk g ↔ f ≈ g := quotient.eq

def of_rat (x : ℚ) : ℝ := mk (of_rat x)

instance : has_zero ℝ := ⟨of_rat 0⟩
instance : has_one ℝ := ⟨of_rat 1⟩

theorem of_rat_zero : of_rat 0 = 0 := rfl
theorem of_rat_one : of_rat 1 = 1 := rfl

@[simp] theorem mk_eq_zero {f} : mk f = 0 ↔ lim_zero f :=
by have : mk f = 0 ↔ lim_zero (f - 0) := quotient.eq;
   rwa sub_zero at this

instance : has_add ℝ :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f + g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r] using add_lim_zero hf hg⟩

@[simp] theorem mk_add (f g : cau_seq) : mk f + mk g = mk (f + g) := rfl 

instance : has_neg ℝ :=
⟨λ x, quotient.lift_on x (λ f, mk (-f)) $
  λ f₁ f₂ hf, quotient.sound $
  by simpa [(≈), setoid.r] using neg_lim_zero hf⟩

@[simp] theorem mk_neg (f : cau_seq) : -mk f = mk (-f) := rfl 

instance : has_mul ℝ :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f * g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r, mul_add, mul_comm] using
    add_lim_zero (mul_lim_zero g₁ hf) (mul_lim_zero f₂ hg)⟩

@[simp] theorem mk_mul (f g : cau_seq) : mk f * mk g = mk (f * g) := rfl 

theorem of_rat_add (x y : ℚ) : of_rat (x + y) = of_rat x + of_rat y :=
congr_arg mk (of_rat_add _ _)

theorem of_rat_neg (x : ℚ) : of_rat (-x) = -of_rat x :=
congr_arg mk (of_rat_neg _)

theorem of_rat_mul (x y : ℚ) : of_rat (x * y) = of_rat x * of_rat y :=
congr_arg mk (of_rat_mul _ _)

instance : comm_ring ℝ :=
by refine { neg := has_neg.neg,
    add := (+), zero := 0, mul := (*), one := 1, .. };
  { repeat {refine λ a, quotient.induction_on a (λ _, _)},
    simp [show 0 = mk 0, from rfl, show 1 = mk 1, from rfl,
          mul_left_comm, mul_comm, mul_add] }

theorem of_rat_sub (x y : ℚ) : of_rat (x - y) = of_rat x - of_rat y :=
congr_arg mk (of_rat_sub _ _)

instance : has_lt ℝ :=
⟨λ x y, quotient.lift_on₂ x y (<) $
  λ f₁ g₁ f₂ g₂ hf hg, propext $
  ⟨λ h, lt_of_eq_of_lt (setoid.symm hf) (lt_of_lt_of_eq h hg),
   λ h, lt_of_eq_of_lt hf (lt_of_lt_of_eq h (setoid.symm hg))⟩⟩

@[simp] theorem mk_lt {f g : cau_seq} : mk f < mk g ↔ f < g := iff.rfl

@[simp] theorem mk_pos {f : cau_seq} : 0 < mk f ↔ pos f :=
iff_of_eq (congr_arg pos (sub_zero f))

instance : has_le ℝ := ⟨λ x y, x < y ∨ x = y⟩

@[simp] theorem mk_le {f g : cau_seq} : mk f ≤ mk g ↔ f ≤ g :=
or_congr iff.rfl quotient.eq

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b :=
quotient.induction_on₃ a b c (λ f g h,
  iff_of_eq (congr_arg pos $ by rw add_sub_add_left_eq_sub))

instance : linear_order ℝ :=
{ le := (≤), lt := (<),
  le_refl := λ a, or.inr rfl,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ f g h, by simpa using le_trans,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa using lt_iff_le_not_le,
  le_antisymm := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa [mk_eq] using @cau_seq.le_antisymm f g,
  le_total := λ a b, quotient.induction_on₂ a b $
    λ f g, by simpa using le_total f g }

theorem of_rat_lt {x y : ℚ} : of_rat x < of_rat y ↔ x < y :=
show pos _ ↔ _, by rw [← cau_seq.of_rat_sub, of_rat_pos, sub_pos]

protected theorem zero_lt_one : (0 : ℝ) < 1 := of_rat_lt.2 zero_lt_one

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
quotient.induction_on₂ a b $ λ f g, by simpa using cau_seq.mul_pos

instance : linear_ordered_comm_ring ℝ :=
{ add_le_add_left := λ a b h c,
    (le_iff_le_iff_lt_iff_lt.2 $ real.add_lt_add_iff_left c).2 h,
  zero_ne_one := ne_of_lt real.zero_lt_one,
  mul_nonneg := λ a b a0 b0,
    match a0, b0 with
    | or.inl a0, or.inl b0 := le_of_lt (real.mul_pos a0 b0)
    | or.inr a0, _ := by simp [a0.symm]
    | _, or.inr b0 := by simp [b0.symm]
    end,
  mul_pos := @real.mul_pos,
  zero_lt_one := real.zero_lt_one,
  add_lt_add_left := λ a b h c, (real.add_lt_add_iff_left c).2 h,
  ..real.comm_ring, ..real.linear_order }

local attribute [instance] classical.prop_decidable

noncomputable instance : has_inv ℝ :=
⟨λ x, quotient.lift_on x
  (λ f, mk $ if h : lim_zero f then 0 else inv f h) $
λ f g fg, begin
  have := lim_zero_congr fg,
  by_cases hf : lim_zero f,
  { simp [hf, this.1 hf, setoid.refl] },
  { have hg := mt this.2 hf, simp [hf, hg],
    have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf),
    have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg),
    rw [mk_eq.2 fg, ← Ig] at If,
    rw mul_comm at Ig,
    rw [← mul_one (mk (inv f hf)), ← Ig, ← mul_assoc, If,
        mul_assoc, Ig, mul_one] }
end⟩

@[simp] theorem inv_zero : (0 : ℝ)⁻¹ = 0 :=
congr_arg mk $ by rw dif_pos; [refl, exact zero_lim_zero]

@[simp] theorem inv_mk {f} (hf) : (mk f)⁻¹ = mk (inv f hf) :=
congr_arg mk $ by rw dif_neg

protected theorem inv_mul_cancel {x : ℝ} : x ≠ 0 → x⁻¹ * x = 1 :=
quotient.induction_on x $ λ f hf, begin
  simp at hf, simp [hf],
  exact quotient.sound (cau_seq.inv_mul_cancel hf)
end

noncomputable instance : discrete_linear_ordered_field ℝ :=
{ inv            := has_inv.inv,
  inv_mul_cancel := @real.inv_mul_cancel,
  mul_inv_cancel := λ x x0, by rw [mul_comm, real.inv_mul_cancel x0],
  inv_zero       := inv_zero,
  decidable_le   := by apply_instance,
  ..real.linear_ordered_comm_ring }

@[simp] theorem of_rat_eq_cast : ∀ x : ℚ, of_rat x = x :=
eq_cast of_rat rfl of_rat_add of_rat_mul

theorem archimedean (x : ℝ) : ∃ n : ℕ, x < n :=
quotient.induction_on x $ λ f,
let ⟨M, M0, H⟩ := f.bounded' 0 in
⟨nat_ceil M + 1,
  by rw [← cast_coe_nat, ← of_rat_eq_cast]; exact
  ⟨1, zero_lt_one, 0, λ i _,
    le_sub_left_iff_add_le.2 $ (add_le_add_iff_right _).2 $
    le_trans (le_of_lt (abs_lt.1 (H _)).2) (le_nat_ceil _)⟩⟩

theorem exists_pos_rat_lt {x : ℝ} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q:ℝ) < x :=
let ⟨n, h⟩ := archimedean x⁻¹ in
⟨n.succ⁻¹, inv_pos (nat.cast_pos.2 (nat.succ_pos n)), begin
  rw [rat.cast_inv, inv_eq_one_div,
      div_lt_iff, mul_comm, ← div_lt_iff x0, one_div_eq_inv],
  { apply lt_trans h, simp [zero_lt_one] },
  { simp [-nat.cast_succ, nat.succ_pos] }
end⟩

theorem exists_rat_near' (x : ℝ) {ε : ℚ} (ε0 : ε > 0) :
  ∃ q : ℚ, abs (x - q) < ε :=
quotient.induction_on x $ λ f,
let ⟨i, hi⟩ := f.cauchy (half_pos ε0) in ⟨f i, begin
  rw [← of_rat_eq_cast, ← of_rat_eq_cast],
  refine abs_lt.2 ⟨_, _⟩;
    refine mk_lt.2 ⟨_, half_pos ε0, i, λ j ij, _⟩; simp;
    rw [← sub_left_le_iff_le_add, ← neg_sub, sub_self_div_two],
  { exact le_of_lt (abs_lt.1 (hi _ ij)).1 },
  { have := le_of_lt (abs_lt.1 (hi _ ij)).2,
    rwa [← neg_sub, neg_le] at this }
end⟩

theorem exists_rat_near (x : ℝ) {ε : ℝ} (ε0 : ε > 0) :
  ∃ q : ℚ, abs (x - q) < ε :=
let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0,
    ⟨q, h⟩ := exists_rat_near' x δ0 in ⟨q, lt_trans h δε⟩

theorem exists_rat_btwn {x y : ℝ} (h : x < y) : ∃ q : ℚ, x < q ∧ (q:ℝ) < y :=
let ⟨q, h⟩ := exists_rat_near (x + (y - x) / 2) (half_pos (sub_pos.2 h)),
    ⟨h₁, h₂⟩ := abs_lt.1 h in begin
  refine ⟨q, _, _⟩,
  { rwa [sub_left_lt_iff_lt_add, add_lt_add_iff_right] at h₂ },
  { rwa [neg_lt_sub_iff_lt_add, add_assoc, add_halves, add_sub_cancel'_right] at h₁ }
end

end real

end NEW