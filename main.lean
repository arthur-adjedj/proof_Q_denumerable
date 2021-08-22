import init.logic
import init.data.nat.basic
import logic.basic
import tactic.interactive
import tactic.push_neg
import init.core

universes u1 u2 u3

constant α : Sort u1
constant β : Sort u2
constant γ : Sort u3
constant f : α → β 


def injective {α : Sort u1} {β : Sort u2} (f : α → β ) : Prop :=
      ∀ (x1 x2 : α ), f x1 = f x2 → x1 = x2 


def surjective {α : Sort u1} {β : Sort u2} (f : α → β ) : Prop :=
  ∀ y : β, ∃ x : α, f x = y


def bijective {α : Sort u1} {β : Sort u2} (f : α → β ) : Prop :=
  injective f ∧ surjective f


def in_bijection (A : Sort u1) (B : Sort u2): Prop := ∃ f : A → B , bijective f 


def comp {α : Sort u1} {β : Sort u2} {γ : Sort u3} (f : α → β ) (g : β → γ ) := λx : α , g (f x)


lemma forall_exists_unique_imp_forall_exists {α : Sort u1} {β : Sort u2} {f : α → β } :
  (∀ (y : β), ∃! (x : α), f x = y ) → ∀ (y : β), ∃ (x : α), f x = y :=
  begin
    intros a b,
    apply (exists_of_exists_unique (a b))
  end


lemma fuck_this {α : Sort u1} {β : Sort u2} {f : α → β } {x1 x2 : α} : 
  (∀ (y : β), ∃! (x : α), f x = y ) → f x1 = f x2 → x1 = x2 := 
  begin
    intro sup,
    assume a,
    apply (unique_of_exists_unique (sup (f x2))),
    exact a,
    refl
  end


theorem bijective_equiv {α : Sort u1} {β : Sort u2} (f : α → β ) :
   bijective f ↔ ∀ y : β, ∃! x : α, f x = y :=
  begin
    apply iff.intro,
      intros p y,
      cases ((and.elim_right p) y) with x hx,
      rewrite exists_unique,
      use x,
      apply and.intro,
        exact hx,
        intro x1,
        rewrite (eq.symm hx),
        apply (and.elim_left p),
      intro sup,
        apply and.intro,
          intros x1 x2,
          apply (fuck_this sup),
        intro a,
        apply (exists_of_exists_unique (sup a))
  end


theorem comp_of_inj_inj {α : Sort u1} {β : Sort u2} {γ  : Sort u3}  (f : α → β ) (g : β →  γ ) :
  injective f ∧ injective g → injective (comp f g) :=
    begin
      intro andinj,
      intros x1 x2,
      exact implies.trans (and.elim_right andinj (f x1) (f x2)) (and.elim_left andinj x1 x2)
    end


theorem comp_of_surj_surj {α : Sort u1} {β : Sort u2} {γ  : Sort u3}  (f : α → β ) (g : β →  γ ) :
  surjective f ∧ surjective g → surjective (comp f g) :=
  begin
    intro andsurj,
    intro y,
    cases ((and.elim_right andsurj) y) with x1 hx1,
    cases ((and.elim_left andsurj) x1) with x2 hx2,
    use x2,
    calc
       comp f g x2 = g (f x2) : by refl
              ...  = g x1 : by rewrite hx2
              ... = y : by rewrite hx1
  end


theorem comp_of_bij_bij {α : Sort u1} {β : Sort u2} {γ  : Sort u3}  (f : α → β) (g : β →  γ) :
  bijective f ∧ bijective g → bijective (comp f g) :=
  begin
    intro hyp,
    apply and.intro,
      apply comp_of_inj_inj,
        apply and.intro,
          apply and.elim_left (and.elim_left hyp),
          apply and.elim_left (and.elim_right hyp),
      apply comp_of_surj_surj,
        apply and.intro,
          apply and.elim_right (and.elim_left hyp),
          apply and.elim_right (and.elim_right hyp)
  end


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



noncomputable def inverse {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : β → α :=
  begin
    intro y,
    apply  (((iff.elim_left (bijective_equiv f)) p) y ).some
  end


/- theorem inv_bij {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : bijective (inverse f p) :=
  begin
    apply and.intro,
      intros x1 x2,
      rewrite(push_neg.classical.implies_iff_not_or),


      
  end -/


axiom inv_bij {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : bijective (inverse f p)

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


def fst {A : Sort u1} {B : Sort u2}  (x1 : pprod A B) : A := x1.1


theorem map_eq {A : Sort u1} {B : Sort u2} (f : A → B) (x1 x2 : A) :  x1 = x2 → f x1 = f x2 :=
  begin
    intro a,
    rewrite a 
  end


theorem tf {A : Sort u1} {B : Sort u2} (x3 x4 :pprod A  B) : x3 = x4 ↔ x3.1 = x4.1 ∧ x3.2 = x4.2 :=
  begin
    apply iff.intro,
      intro a,
      apply and.intro,
        apply map_eq (λ x :pprod A  B, x.1) x3 x4 a,
        apply map_eq (λ x :pprod A B, x.2) x3 x4 a,
      
      
  end 





theorem prod_bij_prod {A : Sort u1} {B : Sort u2} (f : A → B) (C : Sort u3) [bijective f]  :
  bijective (prod_func_left f C) :=
  begin
    apply and.intro,
      intros x1 x2,
      rewrite prod_func_left,
      simp,
      intro h,
      apply _inst_1.left x1.fst x2.fst
          ((tf.left (prod_func_left f C x1) (prod_func_left f C x2) h).left)
      

      
      
  end 



