import tactic.finish
import biject

universes u1 u2 u3


def id_bij {α : Sort u1 } : bijective (id : α → α ) :=  
  begin
   apply and.intro,
        intros x1 x2,
        simp,
        intro y,
      apply exists.intro,
      rewrite id 
  end


theorem bij_refl : reflexive in_bijection :=
  begin
    intro A,
      apply exists.intro,
      apply id_bij,
  end


theorem bij_trans : transitive in_bijection :=
  begin
    intros A B C,
    intros F G,
    cases F with f hf,
    cases G with g hg,
    apply exists.intro,
    apply comp_of_bij_bij f g,
    apply and.intro,
    apply hf,
    apply hg
  end

theorem single_exists_unique {α : Sort u1} {p : α → Prop} :
  (∃! a : α, p a) ↔ nonempty (subsingleton {a : α // p a}) :=
  begin
    split,
      intro hyp,
        apply nonempty.intro,
        apply subsingleton.intro,
        intro u,
        intro b,
        cases u,
        cases b,
        simp,
        apply unique_of_exists_unique hyp u_property b_property,
      intro hyp,
      

  end


noncomputable def inverse {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : β → α :=
  λ y : β, (((iff.elim_left (bijective_equiv f)) p) y ).some



theorem inv_bij {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : bijective (inverse f p) :=
  begin
    apply and.intro,
      intros y1 y2,
      rewrite inverse,
      simp,
      intro u,
      

      


      
  end 


/-axiom inv_bij {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : bijective (inverse f p)-/

theorem bij_sym : symmetric in_bijection :=
  begin
    intros A B,
    intro inbij,
    cases inbij with f hf,
    apply exists.intro,
    apply inv_bij f hf
  end

theorem bij_eq : equivalence in_bijection :=
  begin
    apply and.intro,
      apply bij_refl,
    apply and.intro,
      apply bij_sym,
      apply bij_trans
  end

def denombrable (α : Sort u1) : Prop := 
  in_bijection ℕ α


def prod_func_left {A : Sort u1} {B : Sort u2}  (f : A → B) (C : Sort u3) : pprod A C → pprod B C :=
  λ x : pprod A C , pprod.mk (f (x.fst))  x.snd



theorem map_eq {A : Sort u1} {B : Sort u2} (f : A → B) (x1 x2 : A) :  x1 = x2 → f x1 = f x2 :=
  begin
    intro a,
    rewrite a 
  end


theorem tf_l {A : Sort u1} {B : Sort u2} {x3 x4 :pprod A  B} : x3 = x4 →  x3.1 = x4.1 ∧ x3.2 = x4.2 :=
  begin
        intro a,
        apply and.intro,
          apply map_eq (λ x :pprod A  B, x.1) x3 x4 a,
          apply map_eq (λ x :pprod A B, x.2) x3 x4 a,
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



theorem prod_bij_prod_left {A : Sort u1} {B : Sort u2} (f : A → B) (C : Sort u3) [bijective f]  :
  bijective (prod_func_left f C) :=
  begin
    apply and.intro,
      intros x1 x2,
      rewrite prod_func_left,
      simp,
      intro h,
      apply iff.elim_right (tf x1 x2),
      apply and.intro,
      apply _inst_1.left x1.fst x2.fst
          ((tf (prod_func_left f C x1) (prod_func_left f C x2)).elim_left h).left,
        rewrite (tf_l h).elim_right,

    intro y,
    let x1 := (_inst_1.elim_right y.1).some,
    use pprod.mk x1 y.2,
    rewrite prod_func_left,
    simp,
    apply tf_r,
    simp,
    change x1 with (_inst_1.elim_right y.1).some,
    apply Exists.some_spec (_inst_1.elim_right y.1),
  end 

theorem Z_denumbrable : denombrable ℤ :=
  begin
    let f : ℕ → ℤ  := λ n: ℕ , if is_odd

  end

