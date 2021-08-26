import tactic.interactive



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