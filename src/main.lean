import init.data.nat.basic
import tactic.finish
import tactic.ext
import biject
import init.data.int.basic
import data.int.basic
import data.nat.parity
import tactic.hint


universes u1 u2 u3 u4


def denombrable (α : Sort u1) : Prop := 
  in_bijection ℕ α

theorem tf_l {A : Sort u1} {B : Sort u2} {x3 x4 :pprod A  B} : x3 = x4 →  x3.1 = x4.1 ∧ x3.2 = x4.2 :=
  begin
        intro a,
        apply and.intro,
          apply map_eq (λ x :pprod A  B, x.1) a,
          apply map_eq (λ x :pprod A B, x.2) a,
  end 



theorem tf_r {A : Sort u1} {B : Sort u2} {x3 x4 :pprod A  B} : x3.1 = x4.1 ∧ x3.2 = x4.2 → x3 = x4 :=
  begin
      intro eq1,
      cases eq1 with a b,
      cases x3,
      cases x4,
      finish
  end


theorem tf  {A : Sort u1} {B : Sort u2} (x3 x4 :pprod A  B) : x3 = x4 ↔  x3.1 = x4.1 ∧ x3.2 = x4.2 :=
  begin
    split,
    apply tf_l,
    apply tf_r
  end


def prod_func {A : Sort u1} {B : Sort u2} {C : Sort u3} 
{D : Sort u4} (f : A → B) (g : C → D) : pprod A C → pprod B D :=
  λ x : pprod A C , pprod.mk (f (x.fst))  (g x.snd)

theorem prod_bij_prod_left {A : Sort u1} {B : Sort u2} {C : Sort u3} 
{D : Sort u4} (f : A → B) (g : C → D) [bijective f] [bijective g] :
  bijective (prod_func f g) :=
  begin
    apply and.intro,
      intros x1 x2,
      rewrite prod_func,
      simp,
      intro h,
      apply iff.elim_right (tf x1 x2),
      apply and.intro,
      apply _inst_1.left x1.fst x2.fst
          ((tf (prod_func f g x1) (prod_func f g x2)).elim_left h).left,
      apply _inst_2.left x1.snd x2.snd
          ((tf (prod_func f g x1) (prod_func f g x2)).elim_left h).right,

    intro y,
    let x1 := (_inst_1.elim_right y.1).some,
    let x2 := (_inst_2.elim_right y.2).some,
    use pprod.mk x1 x2,
    rewrite prod_func,
    simp,
    apply tf_r,
    simp,
    change x1 with (_inst_1.elim_right y.1).some,
    change x2 with (_inst_2.elim_right y.2).some,
    split,
    apply Exists.some_spec (_inst_1.elim_right y.1),
    apply Exists.some_spec (_inst_2.elim_right y.2)
  end 


def nat_plus := { n : ℕ // ¬ n = 0}
  
lemma nat_succ_not_zero (n : ℕ) : ¬ n.succ = 0 :=
  begin
    apply not.intro,
    trivial
  end

def succ_plus (n : ℕ ) : nat_plus :=
  ⟨ n.succ,nat_succ_not_zero n⟩ 

lemma not_zero_le (n : ℕ) : ¬ n = 0 ↔ 0 < n :=
  begin
    split,
    apply nat.cases_on n,
    trivial,
    intro m,
    simp,
    apply nat.cases_on n,
    simp,
    intro m,
    simp,
    trivial
  end

lemma bon (n : nat_plus) : n.val.pred.succ = n.val :=
  begin
  apply n.cases_on,
  intros k p,
  simp,
  apply nat.succ_pred_eq_of_pos ((not_zero_le k).elim_left p)
  end


theorem Nplus_denumbrable : denombrable nat_plus :=
  begin
    rewrite [denombrable,in_bijection],
    use succ_plus,
    split,
    intros x1 x2,
    rewrite [succ_plus,succ_plus],
    intro hyp,
    apply subtype.mk.inj,
    simp,
    apply nat.succ.inj (subtype.mk_eq_mk.elim_left hyp),
    exact (λ n : ℕ , true),
    trivial,
    trivial,
    intro y,
    use y.val.pred,
    rewrite succ_plus,
    rewrite eq.symm (subtype.coe_eta y y.property),
    rewrite subtype.mk.inj_eq,
    simp,
    apply bon y
  end


def abs_nat : ℤ → ℕ 
  |(int.of_nat k) := k
  |(int.neg_succ_of_nat k) := k


@[simp] def nat_abs : ℤ → ℕ
| (int.of_nat m) := m
| -[1+ m]    := m.succ

constant h : Prop
constant dh : decidable h
constants a b : α 


lemma if_works {α : Sort u1} {p : Prop} [decidable p] {a b: α} : p →  (ite p a b = a)  :=
  begin
    intro h,
    simp,
    intro nh,
    trivial
  end

lemma if_not_works {α : Sort u1} {p : Prop} [decidable p] {a b: α} : ¬ p →  (ite p a b = b)  :=
  begin
    intro h,
    rewrite eq.symm (ite_not p b a),
    apply if_works,
    exact h
  end

lemma whatever_decidable : decidable (∀ (n : ℕ), 0 ≤ (n : ℤ )) :=
  begin
    simp,
    apply decidable.true
  end


def f : ℕ → ℤ  := λ n: ℕ , (-1) ^n *(n/2)
def g : ℤ → ℕ  := λ z : ℤ, if z ≤  0  then (0-2*(nat_abs z)) else 1+2*(nat_abs z)



lemma leq_two_z_o (n : ℕ) : n<2 → n=0 ∨ n=1 :=
  begin
    cases n,
    tauto,
    intro,
    fconstructor,
    hint
  
      
    
  end

#check @lt_of_mul_lt_mul_left

lemma lt_of_mul_le_mul_left {α : Type u1} [_inst_1 : linear_ordered_semiring α] {a b c : α}:
 c * a < c * b → 0 < c → a < b :=
  begin
    intros h p,
    si
  end



lemma even_succ_not_zero (n : ℕ) (h : even n.succ) : ¬n.succ / 2 = 0 :=
  begin
     apply not.intro,
     have wut : 0 < 2 := by simp,
     rewrite nat.div_eq_zero_iff wut,
     simp at *,
     cases h,
     norm_cast at *,
     intro x,
     safe,
     rewrite eq.symm (nat.one_mul 2) at x,
     rewrite nat.mul_assoc at x,
     have lol :  1 * (2 * h_w) =  (2 * h_w) := by simp,
     rewrite lol at x,
     rewrite nat.mul_comm 1 2 at x,
     rewrite nat.lt_of_mul_le_mul_left at x,

     
  end
/-
theorem comp_fg_is_id : comp g f = id :=
  begin
    rewrite comp,
    change g with λ (z : ℤ), ite (z ≤ 0) (0 - 2 * nat_abs z) (1+2 * nat_abs z),
    change f with λ (n : ℕ), (-1) ^ n * (↑n / 2),
    simp,
    rewrite function.funext_iff,
    intro n,
    simp,
    by_cases even n,
    rewrite nat.neg_one_pow_of_even h,
    simp,
    cases n,
    simp,
    have p : ¬(↑n.succ / 2 ≤  0) := by simp,
    
  end -/


/- theorem Z_denumbrable : denombrable ℤ := 
  begin
    rewrite denombrable,
    rewrite in_bijection,
    use f,
    rewrite [bijective,and_comm],
    split,
    intro x,
    use g x,
    change g with λ (z : ℤ), ite (z ≤ 0) (1 - 2 * nat_abs z) (2 * nat_abs z),
    change f with λ (n : ℕ), (-1) ^ n * (↑n / 2),
    cases x,
    simp,
    apply if_works int.coe_nat_nonneg,


    




    


  end -/

