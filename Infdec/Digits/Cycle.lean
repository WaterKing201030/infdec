import Infdec.Digits.Tails

namespace wkmath
namespace Digits
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

def isCycChild'(x x' y:Digits):=
  match x, x', y with
  | ε, ε, _ => True
  | ε, _::_, _ => False
  | _::_, ε, ε => False
  | xs::xd, ε, ys::yd =>
    have : (xs::xd) <L (xs::xd) ∨ (xs::xd) =L (xs::xd) ∧ cutTails (xs::xd) (ys::yd) <L cutTails (xs::xd) ε := by {
      simp[cutTails]
      exact Or.inr (And.intro (len.eq.refl _) (len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons _ _)))
    }
    isCycChild' (xs::xd) (ys::yd) (ys::yd)
  | xs::xd, xs'::xd', y =>
    have :xs <L xs::xd ∨ xs =L (xs::xd) ∧ cutTails xs xs' <L cutTails (xs::xd) (xs'::xd'):= Or.inl (len.lt_cons xs xd)
    if xd = xd' then isCycChild' xs xs' y else False
termination_by' {
  rel:=λ x y => (x.fst, cutTails x.fst x.snd.fst).fst <L (y.fst, cutTails y.fst y.snd.fst).fst ∨ ((x.fst, cutTails x.fst x.snd.fst).fst =L (y.fst, cutTails y.fst y.snd.fst).fst ∧ (x.fst, cutTails x.fst x.snd.fst).snd <L (y.fst, cutTails y.fst y.snd.fst).snd)
  wf:=InvImage.wf (λ (x:(_:Digits) ×' (_:Digits) ×' Digits) => (x.fst, cutTails x.fst x.snd.fst)) (len.prod_wf (len.lt.wf))
}

instance explicitInstDecidableIteProp{c t e:Prop}(_ : Decidable c)(_ : Decidable t)(_ : Decidable e):Decidable (if c then t else e):=
  instDecidableIteProp

@[inline] instance isCycChild'.instDecidable{x x' y:Digits}:Decidable (isCycChild' x x' y):=
  match x, x', y with
  | ε, ε, _ => instDecidableTrue
  | ε, _::_, _ => instDecidableFalse
  | _::_, ε, ε => instDecidableFalse
  | xs::xd, ε, ys::yd => by{
    rw[isCycChild']
    have : (xs::xd) <L (xs::xd) ∨ (xs::xd) =L (xs::xd) ∧ cutTails (xs::xd) (ys::yd) <L cutTails (xs::xd) ε := by {
      simp[cutTails]
      exact Or.inr (And.intro (len.eq.refl _) (len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons _ _)))
    }
    exact instDecidable
  }
  | xs::xd, xs'::xd', y => by{
    rw[isCycChild']
    have :xs <L xs::xd ∨ xs =L (xs::xd) ∧ cutTails xs xs' <L cutTails (xs::xd) (xs'::xd'):= Or.inl (len.lt_cons xs xd)
    exact explicitInstDecidableIteProp Digit.instDecidableEq instDecidable instDecidableFalse
  }
termination_by' {
  rel:=λ x y => (x.fst, cutTails x.fst x.snd.fst).fst <L (y.fst, cutTails y.fst y.snd.fst).fst ∨ ((x.fst, cutTails x.fst x.snd.fst).fst =L (y.fst, cutTails y.fst y.snd.fst).fst ∧ (x.fst, cutTails x.fst x.snd.fst).snd <L (y.fst, cutTails y.fst y.snd.fst).snd)
  wf:=InvImage.wf (λ (x:(_:Digits) ×' (_:Digits) ×' Digits) => (x.fst, cutTails x.fst x.snd.fst)) (len.prod_wf (len.lt.wf))
}

def isCycChild(x y:Digits):=
  isCycChild' x ε y

@[inline] instance isCycChild.instDecidable{x y:Digits}:Decidable (isCycChild x y):=
  isCycChild'.instDecidable

def minCyc':Digits → Digits → Digits → Digits
  | _, y, ε => y
  | x, y, zs::zd => if y.isCycChild x then y else minCyc' x ((ε::zd)++y) zs

def minCyc(x:Digits):Digits:=
  minCyc' x ε x

end Digits
end wkmath
