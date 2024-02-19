import Infdec.Digits.Tails

namespace wkmath
namespace Digits

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
  match x, y with
  | ε, ε => True
  | ε, _::_
  | _::_, ε => False
  | xs::xd, ys::yd => isCycChild' (xs::xd) ε (ys::yd)

@[inline] instance isCycChild.instDecidable{x y:Digits}:Decidable (isCycChild x y):=
  match x, y with
  | ε, ε => instDecidableTrue
  | ε, _::_
  | _::_, ε => instDecidableFalse
  | _::_, _::_ => isCycChild'.instDecidable

def minCyc':Digits → Digits → Digits → Digits
  | _, y, ε => y
  | x, y, zs::zd => if y.isCycChild x then y else minCyc' x ((ε::zd)++y) zs

theorem not_ε_minCyc'_not_ε{x:Digits}(h:x ≠ ε){y z:Digits}(h':y ≠ ε ∨ z ≠ ε):minCyc' x y z ≠ ε:=by{
  match z with
  | ε => simp at h'; simp[minCyc']; exact h'
  | z'::zd => {
    rw[minCyc']
    cases Decidable.em (y.isCycChild x) with
    | inl h'' => {
      match x with
      | _::_ => {
        match y with
        | ε => contradiction
        | _::_ => simp[h'']
      }
    }
    | inr h' => {
      simp[h']
      have h':(ε::zd ++ y)≠ε:=by{
        match y with
        | ε | _::_ => simp[append]
      }
      exact not_ε_minCyc'_not_ε h (Or.inl h')
    }
  }
}

def minCyc(x:Digits):Digits:=
  minCyc' x ε x

theorem not_ε_minCyc_not_ε{x:Digits}(h:x ≠ ε):x.minCyc ≠ ε:=by{
  rw[minCyc]
  exact not_ε_minCyc'_not_ε h (Or.inr h)
}

end Digits
end wkmath
