import Infdec.Digits.Zero

namespace wkmath
namespace Digits

def head{x:Digits}(_:x≠ε):Digit:=
  match x with
  | ε::d => d
  | (x'::d)::_ => head (x'::d).noConfusion

def tails{x:Digits}(_:x≠ε):Digits:=
  match x with
  | ε::_ => ε
  | (x'::d')::d => (tails (x'::d').noConfusion)::d

theorem tails_len_eq_heads(x:Digits)(d:Digit):(tails (x::d).noConfusion) =L x:=by{
  induction x generalizing d with
  | nil => rw[tails]; exact len.eq.refl _
  | cons x' d' ih => rw[tails,len.eq]; exact ih d'
}

theorem head.zero_head{x:Digits}(h0:x≠ε)(h1:x.isZero):head h0=(0):=by{
  induction x with
  | nil => contradiction
  | cons x' d ih =>{
    cases x' with
    | nil => {
      simp[head]
      exact h1.right
    }
    | cons x'' d' => {
      simp[head]
      rw[isZero] at h1
      exact ih (x''::d').noConfusion h1.left
    }
  }
}

theorem tails.zero_tails{x:Digits}(h0:x≠ε)(h1:x.isZero):(tails h0).isZero:=by{
  induction x with
  | nil => contradiction
  | cons x' d ih => {
    cases x' with
    | nil => {
      simp[tails,isZero]
    }
    | cons x'' d' => {
      rw[isZero] at h1
      have ih:=ih (x''::d').noConfusion h1.left
      simp[tails,isZero,h1.right]
      exact ih
    }
  }
}

theorem head.cons_head{x:Digits}(h:x≠ε)(d:Digit):head h=head (x::d).noConfusion:=by{
  induction x generalizing d with
  | nil => contradiction
  | cons x' d' ih =>{
    cases x' with
    | nil => {
      simp[head]
    }
    | cons x'' d'' =>{
      simp[head]
    }
  }
}

theorem tails.cons_tails{x:Digits}(h:x≠ε)(d:Digit):(tails h).cons d = tails (x::d).noConfusion:=by{
  induction x generalizing d with
  | nil => contradiction
  | cons x' d' ih => {
    cases x' with
    | nil => {
      simp[tails]
    }
    | cons x'' d'' => {
      simp[tails]
    }
  }
}

theorem tails.append_tails{x:Digits}(h:x≠ε)(y:Digits):(tails h) ++ y = tails (not_ε_append h _:x ++ y ≠ ε):=by{
  induction y with
  | nil => simp
  | cons y' _ ih => {
    simp[append]
    simp[←cons_tails (not_ε_append h _:x ++ y' ≠ ε)]
    exact ih
  }
}

theorem tails_len_lt{x:Digits}(h:x≠ε):tails h <L x:=by{
  induction x with
  | nil => contradiction
  | cons x' d' ih => {
    cases x' with
    | nil => simp[tails, len.lt]
    | cons x'' d'' => simp[tails, len.lt]; exact ih Digits.noConfusion
  }
}

theorem append.tails(x:Digits)(d:Digit):tails (not_ε_append (ε::d).noConfusion x) = x := by{
  induction x with
  | nil => simp[append]; rw[tails]
  | cons xs xd ih => {
    simp[append]
    cases xs with
    | nil => {
      rw[tails,tails]
    }
    | cons xs' xd' => {
      rw[tails]
      simp[append] at ih
      rw[ih]
    }
  }
}

theorem append.head(x:Digits)(d:Digit):head (not_ε_append (ε::d).noConfusion x) = d:=by{
  induction x with
  | nil => simp[append];rw[head]
  | cons xs xd ih => {
    cases xs with
    | nil => {
      rw[head,head]
    }
    | cons xs' xd' =>{
      rw[head]
      simp[append] at ih
      rw[ih]
    }
  }
}

theorem cons_len_eq_append_head(x:Digits)(d:Digit):x::d =L ((ε::d).append x):=by{
  induction x generalizing d with
  | nil => rw[append]; exact len.eq.refl _
  | cons x' xd ih => {
    rw[append,len.eq]
    have h:x'::xd =L x'::d :=by rw[len.eq]; exact len.eq.refl x'
    exact h.trans (ih d)
  }
}

theorem eq_head_append_tails{x:Digits}(h:x≠ε):(ε::(head h)).append (tails h)=x:=by{
  induction x with
  | nil => contradiction
  | cons xs xd ih => {
    cases xs with
    | nil => rw[head,tails,append]
    | cons xs' xd' => {
      rw[head, tails, append]
      simp
      exact ih ((xs'::xd').noConfusion)
    }
  }
}

theorem tails.induction'.{u}
  {P:Digits → Sort u}
  (base:P nil)
  (ind:∀(x:Digits)(d:Digit),P (tails (x::d).noConfusion) → P (x::d))
  (x:Digits)
  : P x := by{
    apply len.induction
    case base => exact base
    case ind => {
      intro x' d' hk x'' he
      match x'' with
      | cons x''' d''' => {
        rw[len.eq] at he
        have ht:=(tails_len_eq_heads x''' d''').trans he
        exact ind x''' d''' (hk (tails (x'''::d''').noConfusion) ht)
      }
    }
  }

theorem reverseInduction.{u}
  {P: Digits → Sort u}
  (base: P nil)
  (ind:∀(d:Digit)(x:Digits), P x → P ((ε::d).append x))
  (x:Digits)
  : P x := by{
    induction x using tails.induction' with
    | base => exact base
    | ind x d ih => {
      let hd:=head (x::d).noConfusion
      let tl:=tails (x::d).noConfusion
      have ind:=ind hd tl ih
      rw[eq_head_append_tails] at ind
      exact ind
    }
  }

theorem tails.recursion.{u}
  {P:Digits → Sort u}
  (base:P ε)
  (ind:(x:Digits)→(h:x≠ε)→P (tails h)→P x)
  (x:Digits)
  : P x := by{
    induction x using reverseInduction with
    | base => exact base
    | ind d x' ih => {
      have h:=not_ε_append (ε::d).noConfusion x'
      have h':=append.tails x' d
      have ind := ind ((ε::d).append x') h
      have h'':tails h = x':=h'
      rw[h''] at ind
      exact ind ih
    }
  }

theorem head_of_head_append_tails(d:Digit)(x:Digits):head (not_ε_append Digits.noConfusion x:ε::d ++ x ≠ ε) = d:=by{
  induction x with
  | nil => simp[head]
  | cons x' d' ih => {
    simp[append]
    rw[←head.cons_head (not_ε_append Digits.noConfusion x':ε::d ++ x' ≠ ε)]
    exact ih
  }
}

theorem tails_of_head_append_tails(d:Digit)(x:Digits):tails (not_ε_append Digits.noConfusion x:ε::d ++ x ≠ ε) = x:=by{
  induction x with
  | nil => simp[tails]
  | cons x' d' ih => {
    simp[append]
    rw[←tails.cons_tails (not_ε_append Digits.noConfusion x':ε::d ++ x' ≠ ε)]
    simp
    exact ih
  }
}

def isTails(y x:Digits):Prop:=
  if h:x=nil then
    False
  else
    y = tails h

@[inline] instance isTails.instDecidable{x y:Digits}:Decidable (y.isTails x):=
  match x with
  | nil => instDecidableFalse
  | cons _ _ => instDecidableEq

@[inline] instance isTails.wf:WellFounded isTails:=by{
  apply WellFounded.intro
  intro x
  apply Acc.intro
  induction x using tails.recursion with
  | base => {
    intro y h
    contradiction
  }
  | ind x he ih => {
    intro y h
    apply Acc.intro
    rw[isTails] at h
    simp[he] at h
    have h: y = tails he := h
    rw[←h] at ih
    exact ih
  }
}

@[inline] instance isTails.instWF:WellFoundedRelation Digits:={
  rel:=isTails
  wf:=wf
}

def cutTails:Digits → Digits → Digits
  | x, ε => x
  | ε, _::_ => ε
  | x::_, y::_ => cutTails x y

theorem cutTails_len_le(x y:Digits):cutTails x y ≤L x:=by{
  match x with
  | ε => match y with
    | ε
    | _::_ => rw[cutTails]; exact len.ε_le _
  | _::_ => match y with
    | ε => rw[cutTails]; exact len.le.refl _
    | _::_ => rw[cutTails]; exact (len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons _ _)).to_le
}

def cutTailsLt(x y:Digits × Digits):=
  cutTails x.fst x.snd <L cutTails y.fst y.snd

@[inline] instance cutTailsLt.wf:WellFounded cutTailsLt:=
  InvImage.wf (λ (x:Digits × Digits) => cutTails x.fst x.snd) len.lt.wf


theorem len_eq_cutTails_eq_ε{x y:Digits}(h:x =L y):cutTails x y = ε:=by{
  match x, y with
  | ε, ε => rfl
  | _::_, _::_ => {
    rw[cutTails]
    rw[len.eq] at h
    exact len_eq_cutTails_eq_ε h
  }
}

theorem len_lt_cutTails_eq_ε{x y:Digits}(h:x <L y):cutTails x y = ε:=by{
  match x, y with
  | ε, _::_ => rfl
  | _::_, _::_ => {
    rw[cutTails]
    rw[len.lt] at h
    exact len_lt_cutTails_eq_ε h
  }
}

theorem len_le_cutTails_eq_ε{x y:Digits}(h:x ≤L y):cutTails x y = ε:=
  h.to_eq_or_lt.elim len_eq_cutTails_eq_ε len_lt_cutTails_eq_ε

theorem len.eq_append_of_cutTails_eq{x y:Digits}(h:x ≤L y)(z:Digits)(h':y =L z ++ x):cutTails y x =L z:=by{
  match x, y with
  | ε, _ => {
    simp[cutTails] at *
    exact h'
  }
  | _::_, _::_ => {
    simp[append, eq, cutTails, le] at *
    exact eq_append_of_cutTails_eq h z h'
  }
}

theorem len.cutTails_eq_of_eq_append{x y:Digits}(h:x ≤L y)(z:Digits)(h':cutTails y x =L z):y =L z ++ x:=by{
  match x, y with
  | ε, _ => {
    simp[cutTails] at *
    exact h'
  }
  | _::_, _::_ => {
    simp[append, eq, cutTails, le] at *
    exact cutTails_eq_of_eq_append h z h'
  }
}

theorem len.cutTails_eq_iff_eq_append{x y:Digits}(h:x ≤L y)(z:Digits):(cutTails y x) =L z ↔ y =L z ++ x:=
  Iff.intro (cutTails_eq_of_eq_append h z) (eq_append_of_cutTails_eq h z)

theorem len.cutTails_lt_of_lt_append{x y:Digits}(h:x ≤L y)(z:Digits)(h':y <L z ++ x):cutTails y x <L z:=by{
  match x, y with
  | ε, _ => {
    simp[cutTails] at *
    exact h'
  }
  | _::_, _::_ => {
    simp[le, append, lt, cutTails] at *
    exact cutTails_lt_of_lt_append h z h'
  }
}

theorem len.lt_append_of_cutTails_lt{x y:Digits}(h:x ≤L y)(z:Digits)(h':cutTails y x <L z):y <L z ++ x:=by{
  match x, y with
  | ε, _ => {
    simp[cutTails] at *
    exact h'
  }
  | _::_, _::_ => {
    simp[le, append, lt, cutTails] at *
    exact lt_append_of_cutTails_lt h z h'
  }
}

theorem len.cutTails_lt_iff_lt_append{x y:Digits}(h:x ≤L y)(z:Digits):(cutTails y x) <L z ↔ y <L z ++ x:=
  Iff.intro (lt_append_of_cutTails_lt h z) (cutTails_lt_of_lt_append h z)

theorem append_cutTails_cancel(x y:Digits):cutTails (x ++ y) y = x:=by{
  induction y with
  | nil => simp[cutTails]
  | cons x' _ ih => simp[cutTails, append, ih]
}

theorem cutTails_append_len_cancel{x y:Digits}(h:y ≤L x):(cutTails x y) ++ y =L x:=by{
  induction y generalizing x with
  | nil => simp[cutTails]; exact len.eq.refl _
  | cons y' _ ih => {
    match x with
    | x'::_ => {
      rw[append]
      simp[len.eq, cutTails]
      simp[len.le] at h
      exact ih h
    }
  }
}

theorem len.prod_wf{α:Type u}{r:α → α → Prop}(wf:WellFounded r):WellFounded (λ (a b:Digits × α) => a.fst <L b.fst ∨ (a.fst =L b.fst ∧ r a.snd b.snd)):=by{
  apply WellFounded.intro
  intro ⟨x0, x1⟩
  have ac1:=wf.apply x1
  have ac0:=lt.wf.apply x0
  induction ac0 generalizing x1 with
  | intro y0 _ ih0 => {
    induction ac1 with
    | intro y1 _ ih1 => {
      apply Acc.intro (y0, y1)
      intro ⟨z0,z1⟩ hz
      cases hz with
      | inl hz => {
        simp at hz
        apply ih0
        exact hz
        exact wf.apply z1
      }
      | inr hz => {
        simp at hz
        have heq{x0 y0:Digits}(heq:x0 =L y0)(z:α)(ac:Acc (λ a b => a.fst <L b.fst ∨ a.fst =L b.fst ∧ r a.snd b.snd) (x0, z)):Acc (λ a b => a.fst <L b.fst ∨ a.fst =L b.fst ∧ r a.snd b.snd) (y0, z):=by{
          apply Acc.intro
          intro ⟨z0,z1⟩ hlt
          simp at hlt
          cases hlt with
          | inl hlt => {
            exact ac.inv (Or.inl (lt_of_lt_of_eq hlt heq.symm))
          }
          | inr hlt => {
            have hlt:=And.intro (hlt.left.trans heq.symm) hlt.right
            exact ac.inv (Or.inr hlt)
          }
        }
        apply heq hz.left.symm z1
        apply ih1
        exact hz.right
      }
    }
  }
}

def getTails:Digits → Digits → Digits
  | ε, ε => ε
  | ε, _::_ => ε
  | _::_, ε => ε
  | xs::xd, rs::_ => (getTails xs rs)::xd

theorem getTails_short_eq{x r:Digits}(h:x ≤L r):getTails x r = x:=
  match x, r with
  | ε, ε
  | ε, _::_ => rfl
  | _::_, _::_ => by{
    rw[len.le] at h
    rw[getTails]
    simp
    exact getTails_short_eq h
  }

theorem getTails_long_len_eq{x r:Digits}(h:r ≤L x):getTails x r =L r:=
  match x, r with
  | ε, ε
  | _::_, ε => len.eq.refl _
  | _::_, _::_ => by{
    rw[len.le] at h
    rw[getTails, len.eq]
    exact getTails_long_len_eq h
  }

theorem getTails_len_le(x y:Digits):getTails x y ≤L y:=
  (len.le_or_gt x y).elim (λ h => by{
    rw[getTails_short_eq h]
    exact h
  }) (λ h => (getTails_long_len_eq h.to_le).to_le)

theorem cutTails_append_getTails(x y:Digits):(cutTails x y)++(getTails x y) = x:=
  match x, y with
  | ε, ε
  | ε, _::_
  | _::_, ε => rfl
  | _::_, _::_ => by{
    rw[cutTails, getTails, append]
    simp
    exact cutTails_append_getTails _ _
  }

def padheadzero'{x y:Digits}(h:x <L y):Digits:=
  if h':ε::(0) ++ x =L y then
    ε::(0) ++ x
  else
    have h':ε::(0) ++ x <L y:=(len.le_iff_eq_or_lt.mp ((len.lt_iff_cons_le _ _ (0)).mp h)).elim (λ h'' => (h' ((cons_len_eq_append_head x (0)).symm.trans h'')).elim) (λ h'' => len.lt_of_eq_of_lt (cons_len_eq_append_head x (0)).symm h'')
    have : cutTailsLt (y,(ε::(0) ++ x)) (y,x):=by{
      rw[cutTailsLt]
      simp
      rw[len.cutTails_lt_iff_lt_append h'.to_le]
      apply λ h => len.lt_of_lt_of_eq h (append.len_eq_congr (len.eq.refl _) (append.len_eq_comm _ _))
      rw[←append.assoc, append, append]
      apply len.lt_of_lt_of_eq (len.lt_cons y (0))
      rw[len.eq]
      exact (cutTails_append_len_cancel h.to_le).symm
    }
    padheadzero' h'
termination_by' {
  rel:=λ (x y:(_:Digits) ×' (_:Digits) ×' _) => cutTailsLt (x.snd.fst, x.fst) (y.snd.fst, y.fst)
  wf:=InvImage.wf (λ x:(_:Digits) ×' (_:Digits) ×' _ => (x.snd.fst, x.fst)) cutTailsLt.wf
}

theorem padheadzero'_len_eq{x y:Digits}(h:x <L y):padheadzero' h =L y:=by{
  cases Decidable.em (ε::(0) ++ x =L y) with
  | inl h' => {
    rw[padheadzero']
    simp[h']
  }
  | inr h' => {
    rw[padheadzero']
    simp[h']
    have h':ε::(0) ++ x <L y:=(len.le_iff_eq_or_lt.mp ((len.lt_iff_cons_le _ _ (0)).mp h)).elim (λ h'' => (h' ((cons_len_eq_append_head x (0)).symm.trans h'')).elim) (λ h'' => len.lt_of_eq_of_lt (cons_len_eq_append_head x (0)).symm h'')
    have : cutTailsLt (y,(ε::(0) ++ x)) (y,x):=by{
      rw[cutTailsLt]
      simp
      rw[len.cutTails_lt_iff_lt_append h'.to_le]
      apply λ h => len.lt_of_lt_of_eq h (append.len_eq_congr (len.eq.refl _) (append.len_eq_comm _ _))
      rw[←append.assoc, append, append]
      apply len.lt_of_lt_of_eq (len.lt_cons y (0))
      rw[len.eq]
      exact (cutTails_append_len_cancel h.to_le).symm
    }
    exact padheadzero'_len_eq h'
  }
}
termination_by' {
  rel:=λ (x y:(_:Digits) ×' (_:Digits) ×' _) => cutTailsLt (x.snd.fst, x.fst) (y.snd.fst, y.fst)
  wf:=InvImage.wf (λ x:(_:Digits) ×' (_:Digits) ×' _ => (x.snd.fst, x.fst)) cutTailsLt.wf
}

def padheadzero{x y:Digits}(h:x ≤L y):Digits:=
  if h':x =L y then
    x
  else
    have h':x <L y:=by{
      rw[len.le_iff_eq_or_lt] at h
      simp[h'] at h
      exact h
    }
    padheadzero' h'

theorem padheadzero_len_eq{x y:Digits}(h:x ≤L y):padheadzero h =L y:=by{
  cases h.to_eq_or_lt with
  | inl h => {
    rw[padheadzero]
    simp[h]
  }
  | inr h => {
    rw[padheadzero]
    simp[h.to_ne.elim]
    exact padheadzero'_len_eq h
  }
}

def heads{x:Digits}(_:x ≠ ε):Digits:=
  match x with
  | x'::_ => x'

def tail{x:Digits}(_:x ≠ ε):Digit:=
  match x with
  | _::d => d

theorem eq_heads_cons_tail{x:Digits}(h:x ≠ ε):(heads h)::(tail h) = x:=
  match x with
  | _::_ => rfl

theorem heads_len_cancel{x y:Digits}(h0:x ≠ ε)(h1:y ≠ ε)(h2:x =L y):heads h0 =L heads h1:=by{
  match x, y with
  | _::_, _::_ => simp[heads]; simp[len.eq] at h2; exact h2
}

end Digits
end wkmath
