import tactic.finish
import tactic.ext
import biject
import data.int.parity

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




theorem Z_denumbrable : denombrable ℤ :=
  begin
    let f : ℕ → ℤ  := λ n: ℕ 

  end

