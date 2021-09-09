import tactic.interactive
import tactic.finish
import data.int.parity
import init.function


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


def comp {α : Sort u1} {β : Sort u2} {γ : Sort u3} (f : β → γ ) (g : α  → β  ) := λx : α ,  f (g x)


lemma forall_exists_unique_imp_forall_exists {α : Sort u1} {β : Sort u2} {f : α → β } :
  (∀ (y : β), ∃! (x : α), f x = y ) → ∀ (y : β), ∃ (x : α), f x = y :=
  begin
    intros a b,
    apply (exists_of_exists_unique (a b))
  end


lemma injective_of_bij_equiv {α : Sort u1} {β : Sort u2} {f : α → β } {x1 x2 : α} : 
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
          apply (injective_of_bij_equiv sup),
        intro a,
        apply (exists_of_exists_unique (sup a))
  end


theorem comp_of_inj_inj {α : Sort u1} {β : Sort u2} {γ  : Sort u3}  (f : α → β ) (g : β →  γ ) :
  injective f ∧ injective g → injective (comp g f) :=
    begin
      intro andinj,
      intros x1 x2,
      exact implies.trans (and.elim_right andinj (f x1) (f x2)) (and.elim_left andinj x1 x2)
    end


theorem comp_of_surj_surj {α : Sort u1} {β : Sort u2} {γ  : Sort u3}  (f : α → β ) (g : β →  γ ) :
  surjective f ∧ surjective g → surjective (comp g f) :=
  begin
    intro andsurj,
    intro y,
    cases ((and.elim_right andsurj) y) with x1 hx1,
    cases ((and.elim_left andsurj) x1) with x2 hx2,
    use x2,
    calc
       comp g f x2 = g (f x2) : by refl
              ...  = g x1 : by rewrite hx2
              ... = y : by rewrite hx1
  end


theorem comp_of_bij_bij {α : Sort u1} {β : Sort u2} {γ  : Sort u3}  (f : α → β) (g : β →  γ) :
  bijective f ∧ bijective g → bijective (comp g f) :=
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


lemma map_eq {A : Sort u1} {B : Sort u2} (f : A → B) {x1 x2 : A} :  x1 = x2 → f x1 = f x2 :=
  begin
    intro a,
    rewrite a 
  end



theorem single_exists_unique {α : Type u1} {p : α → Prop} :
  (∃! x : α, p x) ↔ nonempty {x : α // p x} ∧ subsingleton {x : α // p x} :=
  begin
    split,
      intro hyp,
      split,
      use hyp.some,      
      apply hyp.some_spec.left,
      apply subsingleton.intro,
      intros a b,
      apply subtype.eq,
      apply exists_unique.unique hyp a.property b.property,
    intro hyp,
    let sing := hyp.right,
    apply exists_unique.intro,
    let v : {x // p x} := (nonempty.some hyp.left),
    exact v.property,
    intro y,
    intro h,
    let u : {x // p x} := {val := y, property := h},
    apply map_eq subtype.val  (@subsingleton.elim {x : α // p x} sing u (nonempty.some hyp.left))
  end


noncomputable def inverse {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : β → α :=
  λ y : β, (((iff.elim_left (bijective_equiv f)) p) y ).some

constant p : bijective f
constant x: α 




theorem id_inv_left {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : 
  ∀ y : β  , f (inverse f p y) = y :=
  begin
    intro y,
    rewrite inverse,
    simp,
    apply (Exists.some_spec (((iff.elim_left (bijective_equiv f)) p) y )).left
  end


theorem inv_bij {α : Sort u1} {β : Sort u2} (f : α → β) (p : bijective f) : bijective (inverse f p) :=
  begin
    apply iff.elim_right (bijective_equiv (inverse f p)),
    intro y,
    split,
    split,
      simp,
      show (inverse f p (f y) = y),
      rewrite inverse,
      simp,
      apply p.left (Exists.some _) (y) 
        ((Exists.some_spec (inverse._proof_1 f p (f y))).left),
    intro x,
    simp,
    intro hyp,
    have h := (map_eq f hyp),
    rewrite eq.symm (id_inv_left f p x),
    exact h   
  end

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


theorem comp_inj_inj {α : Sort u1} {β : Sort u2} {f : α → β } {g : β → α} : 
  injective (comp f g) → injective g :=
  begin
    contrapose,
    rewrite injective,
    simp,
    intros x1 x2 eq1 neq1,
    rewrite injective,
    simp,
    use x1,
    use x2,
    split,
    rewrite comp,
    simp,
    rewrite eq1,
    exact neq1 
  end



theorem comp_is_id {α : Sort u1} {β : Sort u2} {f : α → β } {g : β → α} : 
comp f g = id → bijective g:=
  begin
    intro hyp,
    split,        
    intros x1 x2,
    intro p,
    let p2 : f (g x1) = f (g x2 ) := by rewrite p,
    let p3 : injective (comp f g) :=
      begin
        rewrite hyp,
        exact id_bij.left
      end,
    apply (comp_inj_inj p3) x1 x2 p,
    intro x,
    use f x,
    sorry


    /- finish,
    let s : surjective g := comp_id_inj_right (function.funext_iff.elim_right hyp),
    intro x,
    use g x,
    rewrite comp at hyp,
    simp at hyp,
    rewrite hyp (g x) -/
    

           end
