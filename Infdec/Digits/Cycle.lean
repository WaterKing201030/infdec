import Infdec.Digits.Tails
import Infdec.Digits.NegOne

namespace wkmath
namespace Digits

-- y 是 x 的子串

def isCycParent'(x x' y:Digits):=
  match x, x', y with
  | ε, ε, _ => True
  | ε, _::_, _ => False
  | _::_, ε, ε => False
  | xs::xd, ε, ys::yd =>
    have : (xs::xd) <L (xs::xd) ∨ (xs::xd) =L (xs::xd) ∧ cutTails (xs::xd) (ys::yd) <L cutTails (xs::xd) ε := by {
      simp[cutTails]
      exact Or.inr (And.intro (len.eq.refl _) (len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons _ _)))
    }
    isCycParent' (xs::xd) (ys::yd) (ys::yd)
  | xs::xd, xs'::xd', y =>
    have :xs <L xs::xd ∨ xs =L (xs::xd) ∧ cutTails xs xs' <L cutTails (xs::xd) (xs'::xd'):= Or.inl (len.lt_cons xs xd)
    xd = xd' ∧ isCycParent' xs xs' y
termination_by' {
  rel:=λ x y => (x.fst, cutTails x.fst x.snd.fst).fst <L (y.fst, cutTails y.fst y.snd.fst).fst ∨ ((x.fst, cutTails x.fst x.snd.fst).fst =L (y.fst, cutTails y.fst y.snd.fst).fst ∧ (x.fst, cutTails x.fst x.snd.fst).snd <L (y.fst, cutTails y.fst y.snd.fst).snd)
  wf:=InvImage.wf (λ (x:(_:Digits) ×' (_:Digits) ×' Digits) => (x.fst, cutTails x.fst x.snd.fst)) (len.prod_wf (len.lt.wf))
}

instance explicitInstDecidableIteProp{c t e:Prop}(_ : Decidable c)(_ : Decidable t)(_ : Decidable e):Decidable (if c then t else e):=
  instDecidableIteProp

@[inline] instance isCycParent'.instDecidable{x x' y:Digits}:Decidable (isCycParent' x x' y):=
  match x, x', y with
  | ε, ε, _ => instDecidableTrue
  | ε, _::_, _ => instDecidableFalse
  | _::_, ε, ε => instDecidableFalse
  | xs::xd, ε, ys::yd => by{
    rw[isCycParent']
    have : (xs::xd) <L (xs::xd) ∨ (xs::xd) =L (xs::xd) ∧ cutTails (xs::xd) (ys::yd) <L cutTails (xs::xd) ε := by {
      simp[cutTails]
      exact Or.inr (And.intro (len.eq.refl _) (len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons _ _)))
    }
    exact instDecidable
  }
  | xs::xd, xs'::xd', y => by{
    rw[isCycParent']
    have :xs <L xs::xd ∨ xs =L (xs::xd) ∧ cutTails xs xs' <L cutTails (xs::xd) (xs'::xd'):= Or.inl (len.lt_cons xs xd)
    have t{p q:Prop}(d0:Decidable p)(d1:Decidable q):Decidable (p ∧ q):=instDecidableAnd
    exact t Digit.instDecidableEq instDecidable
  }
termination_by' {
  rel:=λ x y => (x.fst, cutTails x.fst x.snd.fst).fst <L (y.fst, cutTails y.fst y.snd.fst).fst ∨ ((x.fst, cutTails x.fst x.snd.fst).fst =L (y.fst, cutTails y.fst y.snd.fst).fst ∧ (x.fst, cutTails x.fst x.snd.fst).snd <L (y.fst, cutTails y.fst y.snd.fst).snd)
  wf:=InvImage.wf (λ (x:(_:Digits) ×' (_:Digits) ×' Digits) => (x.fst, cutTails x.fst x.snd.fst)) (len.prod_wf (len.lt.wf))
}

theorem isCycParent'_self(x y:Digits):isCycParent' x x y:=by{
  induction x with
  | nil => simp[isCycParent']
  | cons x' d ih => {
    simp[isCycParent']
    exact ih
  }
}

theorem isCycParent'_append_cancel(x y z:Digits):isCycParent' (x ++ y) y z ↔ isCycParent' x ε z:=by{
  apply Iff.intro
  . {
    intro h
    match y with
    | ε => {
      simp at h
      exact h
    }
    | y'::yd => {
      rw[append] at h
      rw[isCycParent'] at h
      exact (isCycParent'_append_cancel _ _ _).mp h.right
    }
  }
  . {
    intro h
    match y with
    | ε => {
      simp
      exact h
    }
    | y'::yd => {
      rw[append]
      rw[isCycParent']
      simp
      exact (isCycParent'_append_cancel _ _ _).mpr h
    }
  }
}

def isCycParent(x y:Digits):=
  match x, y with
  | ε, ε => True
  | ε, _::_
  | _::_, ε => False
  | xs::xd, ys::yd => isCycParent' (xs::xd) ε (ys::yd)

@[inline] instance isCycParent.instDecidable{x y:Digits}:Decidable (isCycParent x y):=
  match x, y with
  | ε, ε => instDecidableTrue
  | ε, _::_
  | _::_, ε => instDecidableFalse
  | _::_, _::_ => isCycParent'.instDecidable

theorem isCycParent.refl(x:Digits):x.isCycParent x:=by{
  match x with
  | ε => simp
  | _::_ => simp[isCycParent, isCycParent', isCycParent'_self]
}

theorem ε_isCycParent_ε{x:Digits}(_:(ε).isCycParent x):x = ε:=
  match x with
  | ε => rfl
  | _::_ => by contradiction

theorem ε_isCycParent_ε'{x:Digits}(_:x.isCycParent ε):x = ε:=
  match x with
  | ε => rfl
  | _::_ => by contradiction

def minCyc':Digits → Digits → Digits → Digits
  | _, y, ε => y
  | x, y, zs::zd => if x.isCycParent y then y else minCyc' x ((ε::zd)++y) zs

theorem not_ε_minCyc'_not_ε{x:Digits}(h:x ≠ ε){y z:Digits}(h':y ≠ ε ∨ z ≠ ε):minCyc' x y z ≠ ε:=by{
  match z with
  | ε => simp at h'; simp[minCyc']; exact h'
  | z'::zd => {
    rw[minCyc']
    cases Decidable.em (x.isCycParent y) with
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

theorem isCycParent_not_ε_isZero_ε_zero{x:Digits}(h0:x≠ε)(h1:x.isZero):x.isCycParent (ε::(0)):=by{
  induction x with
  | nil => contradiction
  | cons x' d ih => {
    cases x' with
    | nil => {
      rw[isZero] at h1
      rw[h1.right]
      simp[isCycParent]
      rw[isCycParent']
      simp
      rw[isCycParent']
      simp
    }
    | cons x'' d' => {
      rw[isZero, isZero] at *
      rw[h1.left.right] at ih
      rw[h1.right, h1.left.right] at *
      simp at *
      have ih:=ih h1
      simp[isCycParent]
      rw[isCycParent']
      simp
      rw[isCycParent']
      simp
      simp[isCycParent] at ih
      exact ih
    }
  }
}

theorem not_ε_isZero_minCyc{x:Digits}(h0:x ≠ ε)(h1:x.isZero):x.minCyc = ε::(0):=by{
  rw[minCyc]
  match x with | x'::d => {
    rw[minCyc']
    simp[isCycParent]
    match x' with
    | ε => {
      rw[minCyc']
      rw[isZero] at h1
      rw[h1.right]
    }
    | x''::d' => {
      rw[minCyc']
      have h2:=h1
      rw[isZero, isZero] at h1
      rw[h1.right] at *
      rw[h1.left.right] at *
      have h':=isCycParent_not_ε_isZero_ε_zero Digits.noConfusion h2
      simp[h']
    }
  }
}

theorem isZero_minCyc_eq_self{x:Digits}(h0:x.isZero)(h1:x.minCyc = x):x = ε ∨ x = ε::(0) := by{
  cases x with
  | nil => exact Or.inl rfl
  | cons _ _ => exact Or.inr (h1.symm.trans (not_ε_isZero_minCyc Digits.noConfusion h0))
}

theorem isCycParent'.len_unique{x y z a b:Digits}(h0:isCycParent' x y a)(h1:isCycParent' x z b)(h2:y =L z):y = z:=by{
  match x, y, z with
  | _, ε, ε => rfl
  | _, _::_, ε
  | _, ε, _::_
  | ε, _::_, _::_ => contradiction
  | x'::xd, y'::yd, z'::zd => {
    rw[len.eq] at h2
    rw[isCycParent'] at h0 h1
    cases Decidable.em (xd = yd) with
    | inl h => cases Decidable.em (xd = zd) with
      | inl h' => {
        simp
        simp[h.symm.trans h']
        simp[h] at h0
        simp[h'] at h1
        exact isCycParent'.len_unique h0 h1 h2
      }
      | inr h' => simp[h'] at h1
    | inr h => simp[h] at h0
  }
}

theorem isCycParent.len_unique{x y z:Digits}(h0:x.isCycParent y)(h1:x.isCycParent z)(h2:y =L z):y = z:=by{
  match x, y, z with
  | _, ε, ε => rfl
  | _, _::_, ε
  | _, ε, _::_
  | ε, _::_, _::_ => contradiction
  | x'::xd, y'::yd, z'::zd => {
    simp[isCycParent] at h0 h1
    rw[isCycParent'] at h0 h1
    exact isCycParent'.len_unique h0 h1 h2
  }
}

theorem snd_len_le_minCyc'(x y z:Digits):y ≤L minCyc' x y z:=by{
  match z with
  | ε => rw[minCyc']; exact len.le.refl _
  | _::_ => {
    rw[minCyc']
    cases Decidable.em (x.isCycParent y) with
    | inl h => simp[h]; exact len.le.refl _
    | inr h => simp[h]; exact (append.len_le_left_append y (ε::_)).trans (snd_len_le_minCyc' x _ _)
  }
}

theorem minCyc'_len_le_snd_append_thd(x y z:Digits):minCyc' x y z ≤L y ++ z:=by{
  match z with
  | ε => rw[minCyc']; simp; exact len.le.refl _
  | z::zd => {
    rw[minCyc']
    cases Decidable.em (x.isCycParent y) with
    | inl h => simp[h]; exact append.len_le_right_append _ _
    | inr h => {
      simp[h]
      have h':=minCyc'_len_le_snd_append_thd x (ε::zd ++ y) z
      have h'':(ε::zd ++ y) ++ z =L y ++ z :: zd:=by{
        rw[append.assoc]
        apply (append.len_eq_comm _ _).trans
        rw[append,append,append]
        exact len.eq.refl _
      }
      exact len.le_of_le_of_eq h' h''
    }
  }
}

def isPostfixOf:Digits → Digits → Prop
  | ε, ε => True
  | _::_, ε => False
  | ε, _::_ => True
  | x'::xd, y'::yd => xd = yd ∧ x'.isPostfixOf y'

@[inline] instance isPostfixOf.instDecidable{x y:Digits}:Decidable (x.isPostfixOf y):=
  match x, y with
  | ε, ε
  | ε, _::_ => instDecidableTrue
  | _::_, ε => instDecidableFalse
  | a::_, b::_ => have : Decidable (a.isPostfixOf b) := instDecidable
    instDecidableAnd

theorem isPostfixOf.refl(x:Digits):x.isPostfixOf x:=by{
  induction x with
  | nil => simp
  | cons _ _ ih => simp[isPostfixOf]; exact ih
}

theorem isPostfixOf.antisymm{x y:Digits}(h0:x.isPostfixOf y)(h1:y.isPostfixOf x):x = y:=by{
  match x, y with
  | ε, ε => simp
  | _::_, _::_ => {
    rw[isPostfixOf] at h0 h1
    rw[h0.left]
    simp
    exact antisymm h0.right h1.right
  }
}

theorem isPostfixOf.trans{x y z:Digits}(h0:x.isPostfixOf y)(h1:y.isPostfixOf z):x.isPostfixOf z:=by{
  match x, y, z with
  | _::_, ε, _
  | _, _::_, ε
  | ε, _, ε
  | ε, _, _::_ => simp[isPostfixOf] at *
  | _::_, _::_, _::_ => {
    simp[isPostfixOf] at *
    exact ⟨h0.left.trans h1.left, h0.right.trans h1.right⟩
  }
}

theorem isPostfixOf.len_unique{x y z:Digits}(h0:y.isPostfixOf x)(h1:z.isPostfixOf x)(h2:y =L z):y = z:=by{
  match x, y, z with
  | ε, _::_, _
  | ε, _, _::_
  | _, ε, ε
  | _, ε, _::_
  | _, _::_, ε => simp[isPostfixOf, len.eq] at *
  | _::_, _::_, _::_ => {
    simp[isPostfixOf, len.eq] at *
    simp[h0.left.trans h1.left.symm]
    exact len_unique h0.right h1.right h2
  }
}

theorem isPostfixOf_len_le{x y:Digits}(h:y.isPostfixOf x):y ≤L x:=by{
  match x, y with
  | ε, ε
  | _::_, ε => exact len.ε_le _
  | ε, _::_ => contradiction
  | _::_, _::_ => {
    rw[isPostfixOf] at h
    rw[len.le]
    exact isPostfixOf_len_le h.right
  }
}

theorem isPostfixOf_exists_append{x y:Digits}(h:y.isPostfixOf x):∃ z:Digits, z ++ y = x:=by{
  match x, y with
  | x, ε => exact ⟨x,rfl⟩
  | ε, _::_ => contradiction
  | _::_, _::_ => {
    rw[isPostfixOf] at h
    rw[h.left]
    simp[append]
    exact isPostfixOf_exists_append h.right
  }
}

theorem ε_isPostfixOf(x:Digits):(ε).isPostfixOf x:=by{
  match x with
  | ε | _::_ => simp[isPostfixOf]
}

theorem isPostfixOf.upper_total{x y z:Digits}(h0:y.isPostfixOf x)(h1:z.isPostfixOf x):y.isPostfixOf z ∨ z.isPostfixOf y:=by{
  match x, y, z with
  | ε, _::_, _
  | ε, _, _::_ => contradiction
  | _, ε, ε
  | _, ε, _::_
  | _, _::_, ε => simp[isPostfixOf]
  | _::_, _::_, _::_ => {
    simp[isPostfixOf] at *
    simp[h0.left, h1.left] at *
    exact upper_total h0 h1
  }
}

theorem isCycParent'_isPostfixOf{x y z:Digits}(h:isCycParent' x y z):y.isPostfixOf x:=by{
  match x, y, z with
  | _, ε, _ => exact ε_isPostfixOf _
  | ε, _::_, _ => contradiction
  | _::_, _::_, _ => {
    rw[isCycParent'] at h
    rw[h.left]
    simp[isPostfixOf]
    exact isCycParent'_isPostfixOf h.right
  }
}

theorem isCycParent_isPostfixOf{x y:Digits}(h:x.isCycParent y):y.isPostfixOf x:=by{
  match x, y with
  | _, ε => exact ε_isPostfixOf _
  | ε, _::_ => contradiction
  | _::_, _::_ => simp[isCycParent] at h; rw[isCycParent'] at h; exact isCycParent'_isPostfixOf h
}

theorem isCycParent_minCyc'(x y z:Digits):minCyc' x y z = z ++ y ∨ x.isCycParent (minCyc' x y z):=by{
  match z with
  | ε => simp[minCyc']
  | z'::zd => {
    simp[minCyc']
    cases Decidable.em (isCycParent x y) with
    | inl h => simp[h]
    | inr h => {
      simp[h]
      have h:=isCycParent_minCyc' x (ε::zd ++ y) z'
      cases h with
      | inl h => {
        apply Or.inl
        apply h.trans
        rw[←append.assoc]
        rw[append, append]
      }
      | inr h => exact Or.inr h
    }
  }
}

theorem isCycParent_minCyc(x:Digits):x.isCycParent x.minCyc:=by{
  rw[minCyc]
  have h:=isCycParent_minCyc' x ε x
  simp at h
  cases h with
  | inl h => rw[h]; exact isCycParent.refl _
  | inr h => exact h
}

theorem minCyc_isPostfixOf(x:Digits):x.minCyc.isPostfixOf x:=
  isCycParent_isPostfixOf (isCycParent_minCyc x)

theorem minCyc'_len_le_step(x y z:Digits)(d:Digit):minCyc' x y (z::d) ≤L minCyc' x (ε::d ++ y) z:=by{
  rw[minCyc']
  cases Decidable.em (x.isCycParent y) with
  | inl h => simp[h]; exact (append.len_le_left_append _ _).trans (snd_len_le_minCyc' _ _ _)
  | inr h => simp[h]; exact len.le.refl _
}

def replace:Digits → Digits → Digits
  | ε, _ => ε
  | x::_, y => (replace x y) ++ y

theorem replace.pattern_len_eq{x y z:Digits}(h:x =L y):x.replace z = y.replace z:=by{
  match x, y with
  | ε, ε => simp
  | _::_, _::_ => simp[replace]; simp[len.eq] at h; rw[pattern_len_eq h]
}

theorem replace.substr_len_eq{x y z:Digits}(h:y =L z):x.replace y =L x.replace z:=by{
  match x with
  | ε => simp[replace]
  | _::_ => simp[replace]; exact append.len_eq_congr (substr_len_eq h) h
}

theorem ε_replace(x:Digits):(ε).replace x = ε:=
  rfl

theorem replace_ε(x:Digits):x.replace ε = ε:=by{
  induction x with
  | nil => rfl
  | cons _ _ ih => rw[replace]; simp; exact ih
}

theorem replace_isCycParent{x:Digits}(h:x ≠ ε)(y:Digits):(x.replace y).isCycParent y:=by{
  match x with
  | ε::_ => simp[replace]; exact isCycParent.refl _
  | (x'::xd')::xd => {
    match y with
    | ε => rw[replace_ε]; simp
    | y'::yd => {
      rw[replace, append]
      simp[isCycParent]
      rw[isCycParent']
      have he : replace (x' :: xd) (y' :: yd) ++ (y'::yd) = (replace (x' :: xd') (y' :: yd) ++ y')::yd:=rfl
      simp[←he]
      rw[isCycParent'_append_cancel]
      have he:((x'::xd').replace (y'::yd)).isCycParent (y'::yd) ↔ isCycParent' ((x'::xd).replace (y'::yd)) ε (y'::yd):=by{
        rw[replace, append]
        simp[isCycParent]
        rw[replace, append]
        exact Iff.refl _
      }
      rw[←he]
      exact replace_isCycParent Digits.noConfusion _
    }
  }
}

theorem replace_cons_len_eq_replace_append(x y:Digits)(d:Digit):x.replace (y::d) =L x.replace y ++ x:=by{
  induction x with
  | nil => simp[ε_replace]
  | cons _ _ ih => {
    simp[replace, append, len.eq]
    rw[append.assoc]
    apply (append.len_eq_congr ih (len.eq.refl _)).trans
    rw[append.assoc]
    apply append.len_eq_congr (len.eq.refl _)
    exact append.len_eq_comm _ _
  }
}

theorem replace_len_eq_comm(x y:Digits):x.replace y =L y.replace x:=by{
  match x, y with
  | ε, ε
  | ε, _::_
  | _::_, ε => simp[ε_replace, replace_ε]
  | _::_, _::_ => {
    rw[replace]
    apply len.eq.symm
    apply (replace_cons_len_eq_replace_append _ _ _).trans
    apply λ h => append.len_eq_congr h (len.eq.refl _)
    rw[replace]
    apply len.eq.symm
    apply (replace_cons_len_eq_replace_append _ _ _).trans
    apply λ h => append.len_eq_congr h (len.eq.refl _)
    exact replace_len_eq_comm _ _
  }
}

theorem replace_append_left_distrib(x y z:Digits):(x ++ y).replace z = x.replace z ++ y.replace z:=by{
  induction y with
  | nil => simp[ε_replace, append_ε]
  | cons _ _ ih => {
    simp[replace]
    rw[←append.assoc]
    rw[ih]
  }
}

theorem replace_append_right_distrib(x y z:Digits):x.replace (y ++ z) =L x.replace y ++ x.replace z:=by{
  apply (replace_len_eq_comm _ _).trans
  rw[replace_append_left_distrib]
  exact append.len_eq_congr (replace_len_eq_comm _ _) (replace_len_eq_comm _ _)
}

theorem replace.assoc(x y z:Digits):(x.replace y).replace z = x.replace (y.replace z):=by{
  match x with
  | ε => simp[ε_replace]
  | x'::_ => {
    simp[replace, replace_append_left_distrib]
    rw[assoc x']
  }
}

theorem not_ε_replace_len_cancel{x y z:Digits}(hn:x ≠ ε)(he:x.replace y =L x.replace z):y =L z:=by{
  match x with |x'::xd => {
    simp[replace] at he
    match x' with
    | ε => simp[ε_replace] at he; exact he
    | x''::xd' => {
      match y, z with
      | ε, ε => simp
      | ε, _::_
      | _::_, ε => simp[replace_ε, append, len.eq] at he
      | y'::yd, z'::zd => {
        rw[len.eq]
        simp[replace] at he
        repeat rw[append] at he
        rw[len.eq] at he
        have he:=(append.len_eq_comm _ _).trans (he.trans (append.len_eq_comm _ _))
        simp[append, len.eq] at he
        apply not_ε_replace_len_cancel (Digits.noConfusion:(x''::(0))::(0) ≠ ε)
        simp[replace]
        have he:=(append.len_eq_comm _ _).trans (he.trans (append.len_eq_comm _ _))
        repeat rw[append.assoc] at *
        have he:=(append.len_eq_congr (replace_cons_len_eq_replace_append _ _ _) (len.eq.refl _)).symm.trans (he.trans (append.len_eq_congr (replace_cons_len_eq_replace_append _ _ _) (len.eq.refl _)))
        repeat rw[append.assoc] at he
        have he:=(append.len_eq_congr (len.eq.refl _) (append.len_eq_comm _ _)).trans (he.trans (append.len_eq_congr (len.eq.refl _) (append.len_eq_comm _ _)))
        repeat rw[←append.assoc] at he
        have he:=append.len_eq_right_cancel he (len.eq.refl _)
        repeat rw[append.assoc] at he
        exact he
      }
    }
  }
}

theorem replace_not_ε_len_cancel{x y z:Digits}(hn:z ≠ ε)(he:x.replace z =L y.replace z):x =L y:=by{
  have he:=(replace_len_eq_comm _ _).trans (he.trans (replace_len_eq_comm _ _))
  exact not_ε_replace_len_cancel hn he
}

theorem isCycParent'_append_exists{x y z:Digits}(h:isCycParent' x y z):∃ t:Digits, t ++ y = x:=by{
  match x, y, z with
  | ε, ε, _ => exact Exists.intro ε rfl
  | ε, _::_, _
  | _::_, ε, ε => contradiction
  | xs::xd, ε, _::_ => exact Exists.intro (xs::xd) rfl
  | xs::xd, ys::yd, z => {
    rw[isCycParent'] at h
    rw[h.left]
    simp[append]
    exact isCycParent'_append_exists h.right
  }
}

theorem isCycParent_iff_isCycParent'{x y:Digits}{c d:Digit}:isCycParent (x::c) (y::d) ↔ (isCycParent' (x::c) ε (y::d)):=
  by simp[isCycParent]

theorem isCycParent_exists_replace{x y:Digits}(h:x.isCycParent y):∃z:Digits, z.replace y = x ∧ z ≠ ε:=by{
  match h':x, y with
  | ε, ε => exact ⟨ε::(0),rfl,Digits.noConfusion⟩
  | x'::xd, y'::yd => {
    simp[isCycParent] at h
    rw[isCycParent'] at h
    have ⟨t,ht⟩:=isCycParent'_append_exists h
    rw[←ht] at h
    rw[isCycParent'_append_cancel] at h
    match t with
    | ε => {
      apply Exists.intro (ε::(0))
      simp[replace]
      simp at ht
      exact ht
    }
    | ts::td => {
      rw[←isCycParent_iff_isCycParent'] at h
      have : ts::td <L x := by{
        rw[h', ←ht]
        exact append.len_lt_right_append_not_ε _ Digits.noConfusion
      }
      have ⟨z,hz⟩:=isCycParent_exists_replace h
      apply Exists.intro (z::(0))
      simp
      rw[replace, hz.left, ht]
    }
  }
}
termination_by' {
  rel := λ x y => x.fst <L y.fst
  wf := InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) len.lt.wf
}

theorem not_ε_replace_not_ε{x y:Digits}(h0:x ≠ ε)(h1:y ≠ ε):replace x y ≠ ε:=by{
  match x, y with
  | _::_, _::_ => {
    rw[replace, append]
    simp
  }
}

theorem isCycParent.trans{x y z:Digits}(h0:x.isCycParent y)(h1:y.isCycParent z):x.isCycParent z:=by{
  have ⟨a,ha⟩:=isCycParent_exists_replace h0
  have ⟨b,hb⟩:=isCycParent_exists_replace h1
  rw[←hb.left] at ha
  rw[←replace.assoc] at ha
  rw[←ha.left]
  apply replace_isCycParent
  exact not_ε_replace_not_ε ha.right hb.right
}

def rotr:Digits → Digits
  | ε => ε
  | x::d => (ε::d) ++ x

def rotl(x:Digits):Digits:=
  if h : x = ε then
    ε
  else
    (tails h)::(head h)

def rotr'(x:Digits):Digits:=
  if h : x = ε then
    ε
  else
    (ε::tail h)++(heads h)

theorem rotr_iff_rotr':rotr = rotr':=by{
  apply funext
  intro x
  match x with
  | ε => simp
  | _::_ => simp[rotr, rotr', heads, tail]
}

theorem rotr_rotl_cancel(x:Digits):x.rotr.rotl = x:=by{
  match x with
  | ε => simp
  | x::d => {
    simp[rotr]
    rw[rotl]
    simp[not_ε_append (Digits.noConfusion:ε::d ≠ ε) x]
    exact ⟨tails_of_head_append_tails _ _, head_of_head_append_tails _ _⟩
  }
}

theorem rotl_rotr_cancel(x:Digits):x.rotl.rotr = x:=by{
  match x with
  | ε => simp
  | x::d => {
    simp[rotl]
    simp[rotr]
    exact eq_head_append_tails Digits.noConfusion
  }
}

theorem rotr_cancel{x y:Digits}(h:x.rotr = y.rotr):x = y:=by{
  rw[←rotr_rotl_cancel x, ←rotr_rotl_cancel y]
  rw[h]
}

theorem rotl_cancel{x y:Digits}(h:x.rotl = y.rotl):x = y:=by{
  rw[←rotl_rotr_cancel x, ←rotl_rotr_cancel y]
  rw[h]
}

theorem not_ε_rotr{x:Digits}(h:x ≠ ε):x.rotr ≠ ε:=by{
  intro h'
  match x with
  | ε => contradiction
  | _::_ => simp[rotr] at h';exact not_ε_append Digits.noConfusion _ h'
}

theorem not_ε_rotl{x:Digits}(h:x ≠ ε):x.rotl ≠ ε:=by{
  intro h
  have h:=congrArg rotr h
  simp[rotl_rotr_cancel] at h
  simp[rotr] at h
  contradiction
}

theorem rotr_len_eq(x:Digits):x.rotr =L x:=by{
  match x with
  | ε => simp
  | x::d => simp[rotr]; exact (cons_len_eq_append_head _ _).symm
}

theorem rotl_len_eq(x:Digits):x.rotl =L x:=by{
  rw[rotl]
  cases Decidable.em (x = ε) with
  | inl h => simp[h]
  | inr h => simp[h];apply (cons_len_eq_append_head _ _).trans; rw[eq_head_append_tails h]; exact len.eq.refl _
}

theorem rotr_cons_eq_head_append(x:Digits)(d:Digit):(x::d).rotr::d=(ε::d) ++ (x::d):=by{
  simp[rotr, append]
}

theorem replace_rotr_head_eq_tail(x y:Digits)(d:Digit):x.replace (y::d).rotr ++ (ε::d) = (ε::d) ++ x.replace (y::d):=by{
  induction x generalizing y d with
  | nil => simp[replace]
  | cons x' _ ih => {
    simp[replace]
    rw[append.assoc, append, append, rotr_cons_eq_head_append]
    rw[←append.assoc, ←append.assoc, ih]
  }
}

theorem replace_rotr_comm(x y:Digits):x.replace (y.rotr) = (x.replace y).rotr:=by{
  cases x  with
  | nil => simp[replace]
  | cons x' xd => {
    simp[replace]
    match y with
    | ε => simp[replace_ε, rotr]
    | y'::yd => {
      rw[append]
      simp[rotr]
      repeat rw[←append.assoc]
      apply congrArg (λ x:Digits => x ++ y')
      have ht:(y'::yd).rotr = ε::yd ++ y':=rfl
      rw[←ht]
      exact replace_rotr_head_eq_tail _ _ _
    }
  }
}

theorem replace_rotl_comm(x y:Digits):x.replace (y.rotl) = (x.replace y).rotl:=by{
  rw[←rotr_rotl_cancel (x.replace y.rotl)]
  apply congrArg rotl
  rw[←replace_rotr_comm x y.rotl]
  rw[rotl_rotr_cancel]
}

theorem isCycParent_rotr{x y:Digits}(h:x.isCycParent y):x.rotr.isCycParent y.rotr:=by{
  have ⟨z,hz⟩:=isCycParent_exists_replace h
  rw[←hz.left]
  rw[←replace_rotr_comm]
  cases Decidable.em (z = ε) with
  | inl h' => {
    rw[h', replace] at hz
    rw[hz.left.symm] at h
    match y with
    | ε => simp[h']
    | _::_ => contradiction
  }
  | inr h' => exact replace_isCycParent h' _
}

theorem isCycParent_rotr_cancel{x y:Digits}(h:x.rotr.isCycParent y.rotr):x.isCycParent y:=by{
  have ⟨z,hz⟩:=isCycParent_exists_replace h
  rw[←rotr_rotl_cancel x]
  rw[←hz.left]
  rw[←replace_rotl_comm]
  rw[rotr_rotl_cancel]
  cases Decidable.em (z = ε) with
  | inl h' => {
    rw[h', replace] at hz
    rw[hz.left.symm] at h
    match y with
    | ε => simp[h']
    | _::_ => {
      have h:=ε_isCycParent_ε h
      simp[rotr] at h
      exact (not_ε_append Digits.noConfusion _ h).elim
    }
  }
  | inr h' => exact replace_isCycParent h' _
}

theorem isCycParent_rotl{x y:Digits}(h:x.isCycParent y):x.rotl.isCycParent y.rotl:=by{
  rw[←rotl_rotr_cancel x, ←rotl_rotr_cancel y] at h
  exact isCycParent_rotr_cancel h
}

theorem postfix_getTails{x y:Digits}(h:y.isPostfixOf x):x.getTails y = y:=by{
  match x, y with
  | ε, _::_ => contradiction
  | ε, ε
  | _::_, ε => simp[getTails]
  | _::_, _::_ => simp[getTails]; simp[isPostfixOf] at h; exact ⟨postfix_getTails h.right, h.left.symm⟩
}

theorem tails_isPostfixOf{x:Digits}(h:x ≠ ε):(tails h).isPostfixOf x:=by{
  match x with
  | x'::d => {
    induction x' generalizing d with
    | nil => simp[tails, isPostfixOf]
    | cons _ _ ih => {
      simp[isPostfixOf]
      exact ih _ Digits.noConfusion
    }
  }
}

theorem isPostfixOf_len_le_isPostfixOf{x y z:Digits}(h0:y.isPostfixOf x)(h1:z.isPostfixOf x)(h2:z ≤L y):z.isPostfixOf y:=by{
  match x, y, z with
  | ε, _::_, _
  | ε, _, _::_
  | _, ε, _::_ => contradiction
  | _, _, ε => exact ε_isPostfixOf _
  | _::_, _::_, _::_ => {
    rw[len.le] at h2
    rw[isPostfixOf] at *
    exact ⟨h1.left.trans h0.left.symm, isPostfixOf_len_le_isPostfixOf h0.right h1.right h2⟩
  }
}

theorem isPostfixOf_ε{x:Digits}(h:x.isPostfixOf ε):x = ε:=
  match x with
  | ε => rfl
  | _::_ => h.elim

theorem isPostfixOf_append(x y:Digits):x.isPostfixOf (y ++ x):=by{
  match x with
  | ε => exact ε_isPostfixOf _
  | _::_ => simp[isPostfixOf]; exact isPostfixOf_append _ _
}

theorem minCyc'_isMin{x y z:Digits}(h0:z.isPostfixOf y)(h1:y.isPostfixOf x):minCyc' x z (cutTails x z) ≤L minCyc' x y (cutTails x y):=by{
  have ⟨a,ha⟩:=isPostfixOf_exists_append h0
  cases Decidable.em (a = ε) with
  | inl h => {
    rw[h] at ha
    rw[ε_append] at ha
    rw[ha]
    exact len.le.refl _
  }
  | inr h => {
    have h':=eq_head_append_tails h
    have h0':z.isPostfixOf (tails h ++ z):=isPostfixOf_append _ _
    have h1':(tails h ++ z).isPostfixOf x:=by{
      apply λ h => isPostfixOf.trans h h1
      rw[←ha]
      have h'': a ++ z = ((ε::(head h)) ++ (tails h)) ++ z:=by rw[h']
      rw[h'']
      rw[append.assoc]
      exact isPostfixOf_append _ _
    }
    have : (tails h ++ z) <L y:=by{
      rw[←ha]
      apply λ h => append.len_lt_of_len_lt_append_len_le h (len.le.refl _)
      exact tails_len_lt h
    }
    have h2':=minCyc'_isMin h0' h1'
    apply h2'.trans
    have ⟨b,hb⟩:=isPostfixOf_exists_append h1
    rw[←ha, ←h'] at hb
    rw[append.assoc] at hb
    rw[←append.assoc] at hb
    rw[←hb]
    simp[append_cutTails_cancel]
    rw[←h', append.assoc] at ha
    rw[append.assoc]
    rw[←ha]
    simp[append_cutTails_cancel]
    simp[append]
    exact minCyc'_len_le_step _ _ _ _
  }
}
termination_by' {
  rel:=λ x y:(_:Digits) ×' (_:Digits) ×' _ => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' (_:Digits) ×' _ => x.fst) len.lt.wf
}

theorem minCyc_isMin{x y:Digits}(h:x.isCycParent y):x.minCyc ≤L y:=by {
  have h'(z:Digits):minCyc' x y z = y:=by{
    match z with
    | ε => simp[minCyc']
    | _::_ => rw[minCyc']; simp[h]
  }
  have h':=h' (cutTails x y)
  rw[←h']
  rw[minCyc]
  have h'':x = cutTails x ε :=by simp[cutTails]
  have h'':minCyc' x ε x = minCyc' x ε (cutTails x ε):=by rw[←h'']
  rw[h'']
  exact minCyc'_isMin (ε_isPostfixOf _) (isCycParent_isPostfixOf h)
}

theorem minCyc_rotr_len_eq(x:Digits):x.minCyc =L x.rotr.minCyc:=by{
  have ⟨b,hb⟩:=isCycParent_exists_replace (isCycParent_minCyc x.rotr)
  have ⟨a,ha⟩:=isCycParent_exists_replace (isCycParent_minCyc x)
  have ha:=congrArg rotr ha.left
  rw[←replace_rotr_comm] at ha
  have h0:x.rotr.minCyc ≤L x.minCyc:=len.le_of_le_of_eq (minCyc_isMin (isCycParent_rotr (isCycParent_minCyc x))) (rotr_len_eq _)
  have h1:x.minCyc ≤L x.rotr.minCyc:=by{
    rw[replace_rotr_comm] at ha
    have hb:=congrArg rotl hb.left
    rw[←replace_rotl_comm] at hb
    rw[rotr_rotl_cancel] at hb
    have hb':x.isCycParent x.rotr.minCyc.rotl:=by{
      rw[←congrArg (λ y => isCycParent y (rotl (minCyc (rotr x)))) hb]
      cases Decidable.em (b = ε) with
      | inl h => simp[h] at *
      | inr h => exact replace_isCycParent h _
    }
    apply len.le_of_le_of_eq (minCyc_isMin hb')
    exact rotl_len_eq _
  }
  exact (h0.antisymm h1).symm
}

theorem rotr_minCyc_comm(x:Digits):x.minCyc.rotr = x.rotr.minCyc:=by{
  have h0:x.rotr.isCycParent x.minCyc.rotr:=isCycParent_rotr (isCycParent_minCyc x)
  have h1:x.rotr.isCycParent x.rotr.minCyc:=isCycParent_minCyc x.rotr
  have h2:x.minCyc.rotr =L x.rotr.minCyc:=(rotr_len_eq _).trans (minCyc_rotr_len_eq _)
  exact isCycParent.len_unique h0 h1 h2
}

theorem rotl_minCyc_comm(x:Digits):x.minCyc.rotl = x.rotl.minCyc:=by{
  rw[←rotr_rotl_cancel x.rotl.minCyc]
  rw[rotr_minCyc_comm]
  rw[rotl_rotr_cancel]
}

theorem minCyc_rotr_minCyc{x:Digits}(h:x.minCyc = x):x.rotr.minCyc = x.rotr:=by{
  rw[←rotl_rotr_cancel (minCyc _)]
  rw[rotl_minCyc_comm]
  rw[rotr_rotl_cancel]
  rw[h]
}

theorem minCyc_rotl_minCyc{x:Digits}(h:x.minCyc = x):x.rotl.minCyc = x.rotl:=by{
  rw[←rotr_rotl_cancel (minCyc _)]
  rw[rotr_minCyc_comm]
  rw[rotl_rotr_cancel]
  rw[h]
}

theorem isCycParent_len_le{x y:Digits}(h:x.isCycParent y):y ≤L x:=
  isPostfixOf_len_le (isCycParent_isPostfixOf h)

theorem minCyc_len_le(x:Digits):x.minCyc ≤L x:=
  isCycParent_len_le (isCycParent_minCyc x)

theorem minCyc.idemp(x:Digits):x.minCyc.minCyc = x.minCyc:=by{
  have h0:x.isCycParent x.minCyc.minCyc:=(isCycParent_minCyc x).trans (isCycParent_minCyc x.minCyc)
  have h1:=minCyc_isMin h0
  have h2:=isCycParent_minCyc x
  apply isCycParent.len_unique h0 h2
  have h3:=minCyc_len_le x.minCyc
  exact h3.antisymm h1
}

theorem replace_zero_isZero(x:Digits){y:Digits}(h:y.isZero):(x.replace y).isZero:=by{
  induction x with
  | nil => simp[replace]
  | cons _ _ ih => {
    rw[replace]
    exact zero_append_zero_isZero ih h
  }
}

theorem isCycParent_zero_isZero{x y:Digits}(h:y.isZero)(h':x.isCycParent y):x.isZero:=by{
  have ⟨z,hl,_⟩:=isCycParent_exists_replace h'
  rw[←hl]
  exact replace_zero_isZero z h
}

theorem minCyc_tail_eq_tail{x:Digits}(h:x ≠ ε):tail (not_ε_minCyc_not_ε h:x.minCyc ≠ ε) = tail h:=by{
  match x with
  | x'::xd => {
    have h':=not_ε_minCyc_not_ε h
    have ⟨y', yd, hy⟩:=not_ε_exists_cons h'
    have h0:(y'::yd).isPostfixOf (x'::xd):=by{
      rw[←hy]
      exact isCycParent_isPostfixOf (isCycParent_minCyc _)
    }
    simp[isPostfixOf] at h0
    simp[hy]
    simp[tail]
    exact h0.left
  }
}

theorem tail_eq_rotr_head{x:Digits}(h:x ≠ ε):tail h = head (by{intro h'; apply h; have h':=congrArg rotl h'; simp[rotr_rotl_cancel] at h';simp[rotl] at h'; exact h'}:x.rotr ≠ ε):=by{
  match x with
  | _::_ => {
    simp[rotr, tail, head_of_head_append_tails]
  }
}

theorem head_eq_rotl_tail{x:Digits}(h:x ≠ ε):head h = tail (by{intro h'; apply h; have h':=congrArg rotr h'; simp[rotl_rotr_cancel] at h'; simp[rotr] at h'; exact h'}:x.rotl ≠ ε):=by{
  have h':=tail_eq_rotr_head (by{intro h'; apply h; have h':=congrArg rotr h'; simp[rotl_rotr_cancel] at h'; simp[rotr] at h'; exact h'}:x.rotl ≠ ε)
  simp[rotl_rotr_cancel] at h'
  exact h'.symm
}

theorem heads_eq_rotr_tails{x:Digits}(h:x ≠ ε):heads h = tails (by{intro h'; apply h; have h':=congrArg rotl h'; simp[rotr_rotl_cancel] at h';simp[rotl] at h'; exact h'}:x.rotr ≠ ε):=by{
  match x with
  | _::_ => simp[heads, rotr, tails_of_head_append_tails]
}

theorem tails_eq_rotl_heads{x:Digits}(h:x ≠ ε):tails h = heads (by{intro h'; apply h; have h':=congrArg rotr h'; simp[rotl_rotr_cancel] at h'; simp[rotr] at h'; exact h'}:x.rotl ≠ ε):=by{
  have h':=heads_eq_rotr_tails (by{intro h'; apply h; have h':=congrArg rotr h'; simp[rotl_rotr_cancel] at h'; simp[rotr] at h'; exact h'}:x.rotl ≠ ε)
  simp[rotl_rotr_cancel] at h'
  exact h'.symm
}

theorem minCyc_head_eq_head{x:Digits}(h:x ≠ ε):head (not_ε_minCyc_not_ε h:x.minCyc ≠ ε) = head h := by{
  repeat rw[head_eq_rotl_tail]
  simp[rotl_minCyc_comm]
  apply minCyc_tail_eq_tail
}

theorem ε_minCyc_ε{x:Digits}(h:x.minCyc = ε):x = ε:=
  (Decidable.em (x = ε)).elim id (λ h' => (not_ε_minCyc_not_ε h' h).elim)

theorem replace_toZero_comm(x y:Digits):x.replace y.toZero = (x.replace y).toZero:=by{
  induction x with
  | nil => simp[replace]
  | cons _ _ ih => {
    simp[replace] at *
    rw[append_toZero_eq_toZero_append]
    rw[ih]
  }
}

theorem replace_toNegOne_comm(x y:Digits):x.replace y.toNegOne = (x.replace y).toNegOne:=by{
  induction x with
  | nil => simp[replace]
  | cons _ _ ih => {
    simp[replace] at *
    rw[append_toNegOne_eq_toNegOne_append]
    rw[ih]
  }
}

end Digits
end wkmath
