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

def isTails(y x:Digits):Prop:=
  if h:x=nil then
    False
  else
    y = tails h

@[inline] instance isTails.instDecidable{x y:Digits}:Decidable (y.isTails x):=
  match x with
  | nil => instDecidableFalse
  | cons _ _ => instDecidableEq

@[inline] instance isTails.instWF:WellFoundedRelation Digits:={
  rel:=isTails
  wf:=by{
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
}
end Digits
end wkmath
