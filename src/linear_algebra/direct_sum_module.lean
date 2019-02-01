/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings, indexed by a discrete type.
-/

import linear_algebra.basic
import algebra.pi_instances
import data.dfinsupp

universes u v w u₁

variables (R : Type u) [comm_ring R]
variables (ι : Type v) [decidable_eq ι] (β : ι → Type w)
variables [Π i, add_comm_group (β i)] [Π i, module R (β i)]
include R

def direct_sum : Type* := Π₀ i, β i

namespace direct_sum

variables {R ι β}

instance : add_comm_group (direct_sum R ι β) := dfinsupp.add_comm_group
instance : module R (direct_sum R ι β) := dfinsupp.to_module

variables ι β
def mk (s : finset ι) : (Π i : (↑s : set ι), β i.1) →ₗ direct_sum R ι β :=
dfinsupp.lmk β s

def of (i : ι) : β i →ₗ direct_sum R ι β :=
dfinsupp.lsingle β i

lemma single_eq_of (i : ι) (b : β i) :
  dfinsupp.single i b = of ι β i b := rfl

variables {ι β}

theorem mk_inj (s : finset ι) : function.injective (mk ι β s) :=
dfinsupp.mk_inj s

theorem of_inj (i : ι) : function.injective (of ι β i) :=
λ x y H, congr_fun (mk_inj _ H) ⟨i, by simp [finset.to_set]⟩

@[elab_as_eliminator]
protected theorem induction_on {C : direct_sum R ι β → Prop}
  (x : direct_sum R ι β) (H_zero : C 0)
  (H_basic : ∀ (i : ι) (x : β i), C (of ι β i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply dfinsupp.induction x H_zero,
  intros i b f h1 h2 ih,
  solve_by_elim
end

lemma sum_of [Π i, decidable_pred (eq (0 : β i))] (f : direct_sum R ι β) :
  f.sum (λ i, of ι β i) = f :=
by dsimp [of, dfinsupp.lsingle]; unfold_coes; simp;
  exact @dfinsupp.sum_single ι β _ _ _ f

variables {γ : Type u₁} [add_comm_group γ] [module R γ]
variables (φ : Π i, β i →ₗ γ)

def to_module_aux (f : direct_sum R ι β) : γ :=
quotient.lift_on f (λ x, x.2.to_finset.sum $ λ i, φ i (x.1 i)) $ λ x y H,
begin
  have H1 : x.2.to_finset ∩ y.2.to_finset ⊆ x.2.to_finset, from finset.inter_subset_left _ _,
  have H2 : x.2.to_finset ∩ y.2.to_finset ⊆ y.2.to_finset, from finset.inter_subset_right _ _,
  refine (finset.sum_subset H1 _).symm.trans ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _)),
  { intros i H1 H2, rw finset.mem_inter at H2, rw H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(y.3 i).resolve_left (mt (and.intro H1) H2), (φ i).map_zero] },
  { intros i H1, rw H i },
  { intros i H1 H2, rw finset.mem_inter at H2, rw ← H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(x.3 i).resolve_left (mt (λ H3, and.intro H3 H1) H2), (φ i).map_zero] }
end

variables {φ}

theorem to_module_aux.add (f g) :
  to_module_aux φ (f + g) = to_module_aux φ f + to_module_aux φ g :=
begin
  refine quotient.induction_on f (λ x, _),
  refine quotient.induction_on g (λ y, _),
  change finset.sum _ _ = finset.sum _ _ + finset.sum _ _,
  simp only [(φ _).map_add, finset.sum_add_distrib],
  congr' 1,
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inl },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(x.3 i).resolve_left H2, (φ i).map_zero] } },
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inr },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(y.3 i).resolve_left H2, (φ i).map_zero] } }
end

theorem to_module_aux.smul (c f) :
  to_module_aux φ (c • f) = c • to_module_aux φ f :=
begin
  refine quotient.induction_on f (λ x, _),
  refine eq.trans (finset.sum_congr rfl _) finset.smul_sum.symm,
  { intros i h1, dsimp at *, simp [h1, (φ i).map_smul] }
end

variables (ι φ)
def to_module : direct_sum R ι β →ₗ γ :=
⟨to_module_aux φ, to_module_aux.add, to_module_aux.smul⟩
variables {ι φ}

lemma to_module_apply (x) : to_module ι φ x = to_module_aux φ x := rfl

@[simp] lemma to_module.of (i) (x : β i) : to_module ι φ (of ι β i x) = φ i x :=
by dsimp [to_module_apply, to_module_aux, of, dfinsupp.single, dfinsupp.mk, to_module_aux]; simp

variables {ψ : direct_sum R ι β →ₗ γ}
variables (H1 : ∀ (i : ι) (x : β i), ψ (of ι β i x) = to_module ι φ (of ι β i x))

theorem to_module.unique (f : direct_sum R ι β) : ψ f = to_module ι φ f :=
direct_sum.induction_on f
  (ψ.map_zero.trans (to_module _ _).map_zero.symm) H1 $ λ f g ihf ihg,
by rw [ψ.map_add, (to_module _ _).map_add, ihf, ihg]

variables {ψ' : direct_sum R ι β →ₗ γ}
variables (H2 : ∀ i, ψ.comp (of ι β i) = ψ'.comp (of ι β i))

theorem to_module.ext (f : direct_sum R ι β) : ψ f = ψ' f :=
direct_sum.induction_on f (ψ.map_zero.trans ψ'.map_zero.symm)
  (λ i, linear_map.ext_iff.1 (H2 i)) $ λ f g ihf ihg,
by rw [ψ.map_add, ψ'.map_add, ihf, ihg]

def set_to_set (S T : set ι) (H : S ⊆ T) :
  direct_sum R S (β ∘ subtype.val) →ₗ direct_sum R T (β ∘ subtype.val) :=
to_module _ $ λ i, of T (β ∘ @subtype.val _ T) ⟨i.1, H i.2⟩

protected def id (M : Type v) [add_comm_group M] [module R M] :
  direct_sum R punit (λ _, M) ≃ₗ M :=
linear_equiv.of_linear (to_module _ $ λ _, linear_map.id) (of _ (λ _, M) punit.star)
  (linear_map.ext $ λ x, to_module.of _ _)
  (linear_map.ext $ to_module.ext $ λ ⟨⟩, linear_map.ext $ λ m, by dsimp; rw to_module.of; refl)

instance : has_coe_to_fun (direct_sum R ι β) :=
dfinsupp.has_coe_to_fun

def component (ι : Type*) [decidable_eq ι] (β : ι → Type*)
  [Π i, add_comm_group (β i)] [Π i, module R (β i)]
  (i : ι) : direct_sum R ι β →ₗ β i :=
{ to_fun := λ f, f i,
  add := λ _ _, dfinsupp.add_apply,
  smul := λ _ _, dfinsupp.smul_apply }

lemma of_apply (i : ι) (b : β i) : ((of ι β i) b) i = b :=
by rw [of, dfinsupp.lsingle_apply, dfinsupp.single_apply, dif_pos rfl]

lemma apply_eq_component (f : direct_sum R ι β) (i : ι) :
  f i = component ι β i f := rfl

@[simp] lemma component.of_self (i : ι) (b : β i) :
  component ι β i ((of ι β i) b) = b :=
of_apply i b

lemma component.of (i j : ι) (b : β j) :
  component ι β i ((of ι β j) b) =
  if h : j = i then eq.rec_on h b else 0 :=
dfinsupp.single_apply

@[extensionality] lemma ext {f g : direct_sum R ι β}
  (h : ∀ i, component ι β i f = component ι β i g) : f = g :=
dfinsupp.ext h

lemma ext_iff {f g : direct_sum R ι β} : f = g ↔
  ∀ i, component ι β i f = component ι β i g :=
⟨λ h _, by rw h, ext⟩

end direct_sum
