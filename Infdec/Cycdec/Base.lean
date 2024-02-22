import Infdec.Integer
namespace wkmath
structure cyc where
  pre:Digits
  post:Digits
  exp:int
  inv:post ≠ ε

namespace Digits
def headzerocount(x:Digits):Digits:=
  if h:x = ε then ε
  else if head h = (0) then
    have : (tails h) <L x:=tails_len_lt h
    (headzerocount (tails h)).Succ
  else ε
termination_by' {
  rel:=len.lt
  wf:=len.lt.wf
}

theorem notZero_cons_zero_headzerocount_eq{x:Digits}(h:¬x.isZero):(x::(0)).headzerocount = x.headzerocount:=by{
  induction x using tails.recursion with
  | base => contradiction
  | ind x h' ih => {
    have h0:(tails h')::(0) = (tails (Digits.noConfusion:x::(0) ≠ ε)):=tails.cons_tails _ _
    rw[headzerocount, headzerocount]
    simp[h']
    have h1:head h' = head (Digits.noConfusion:x::(0) ≠ ε):=head.cons_head _ _
    cases Decidable.em (head h' = (0)) with
    | inl h'' => {
      rw[←h1]
      simp[h'']
      apply congrArg
      rw[←h0]
      apply ih
      intro hf
      apply h
      rw[←eq_head_append_tails h']
      rw[h'']
      have : (ε::(0)).isZero := by simp
      exact zero_append_zero_isZero this hf
    }
    | inr h'' => rw[←h1]; simp[h'']
  }
}

def headzerocountLt(x y:Digits):=
  x.headzerocount < y.headzerocount

@[inline] instance headzerocountLt.wf:WellFounded headzerocountLt:=
  InvImage.wf (λ x:Digits => x.headzerocount) nat.lt.wf
end Digits

namespace cyc

def Zero:cyc:=⟨ε, ε::(0), ⟨ε, false⟩, Digits.noConfusion⟩

def movl{x:Digits}{d:Digit}(hc:(x::d).minCyc = x::d)(e:int):cyc:=
  if h:x = ε then
    ⟨ε, x::d, e, Digits.noConfusion⟩
  else if h':Digits.head (Digits.noConfusion:x::d ≠ ε) = (0) then
    have hc':(x::d).rotl.minCyc = (x::d).rotl:=Digits.minCyc_rotl_minCyc hc
    have : Digits.headzerocountLt ((x::d).rotl) (x::d):=by{
      have : (x::d).rotl.headzerocount.Succ =N (x::d).headzerocount:=by{
        simp[Digits.rotl] at *
        apply Digits.nat.eq.symm
        rw[Digits.headzerocount]
        simp[h']
        rw[Digits.Succ, Digits.Succ]
        apply λ h => Digits.nat.eq_of_eq_add_eq h (Digits.nat.eq.refl Digits.One)
        have tmp : ¬(Digits.tails (Digits.noConfusion:x::d ≠ ε)).isZero:=by {
          intro hf
          have tmp : ¬ x.isZero:=by{
            rw[←Digits.tails.cons_tails h] at hf
            rw[Digits.isZero] at hf
            simp[hf.right] at *
            rw[Digits.tails.cons_tails Digits.noConfusion] at hc'
            have h'':(Digits.tails (Digits.noConfusion:(x::(0))::(0) ≠ ε)).isZero:=by{
              rw[←Digits.tails.cons_tails]
              rw[←Digits.tails.cons_tails h]
              simp[Digits.isZero]
              exact hf
            }
            rw[h'] at hc'
            have h''':(Digits.tails (Digits.noConfusion:(x::(0))::(0) ≠ ε)) = ε ∨ (Digits.tails (Digits.noConfusion:(x::(0))::(0) ≠ ε)) = ε::(0) := Digits.isZero_minCyc_eq_self h'' hc'
            rw[←Digits.tails.cons_tails Digits.noConfusion] at h'''
            simp at h'''
            rw[←Digits.tails.cons_tails h] at h'''
            contradiction
          }
          apply tmp
          rw[←Digits.eq_head_append_tails h]
          have h':Digits.head h = (0):=by{
            rw[Digits.head.cons_head]
            exact h'
          }
          rw[h']
          have h':(ε::(0)).isZero:=by simp
          rw[←Digits.tails.cons_tails h] at hf
          rw[Digits.isZero] at hf
          exact Digits.zero_append_zero_isZero h' hf.left
        }
        rw[Digits.notZero_cons_zero_headzerocount_eq tmp]
        exact Digits.nat.eq.refl _
      }
      exact Digits.nat.lt_iff_Succ_le.mpr this.to_le
    }
    movl hc' (e + int.One)
  else
    ⟨ε, x::d, e, Digits.noConfusion⟩
termination_by' {
  rel:=λ x y:(_:Digits) ×' (_:Digit) ×' _ => Digits.headzerocountLt (x.fst::x.snd.fst) (y.fst::y.snd.fst)
  wf:=InvImage.wf (λ x:(_:Digits) ×' (_:Digit) ×' _ => x.fst::x.snd.fst) Digits.headzerocountLt.wf
}

def movr(n:Digits)(a:Digit)(x:Digits)(d:Digit)(e:int):cyc:=
  if a = d then
    match h:n with
    | ε => ⟨ε, (x::d).rotr, e + int.One, Digits.not_ε_append Digits.noConfusion _⟩
    | n'::b =>
      have h':(x::d).rotr ≠ ε:=Digits.not_ε_append Digits.noConfusion _
      have : n' <L n:=by rw[h]; exact Digits.len.lt_cons _ _
      movr n' b (Digits.heads h') (Digits.tail h') (e + int.One)
  else
    ⟨n::a, x::d, e, Digits.noConfusion⟩
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.len.lt.wf
}

def toStdCyc(c:cyc):cyc:=
  match c with
  | ⟨n, x::d, e, _⟩ =>
    have hx: (x::d).minCyc ≠ ε := Digits.not_ε_minCyc_not_ε Digits.noConfusion
    have hc: ((Digits.heads hx)::(Digits.tail hx)).minCyc = (Digits.heads hx)::(Digits.tail hx) := by{
      rw[Digits.eq_heads_cons_tail hx]
      exact Digits.minCyc.idemp (x::d)
    }
    if h':n.toStdNat = ε then
      movl hc e.toStdInt
    else
      movr (Digits.heads h') (Digits.tail h') (Digits.heads hx) (Digits.tail hx) e.toStdInt

def eq(x y:cyc):=
  x.toStdCyc = y.toStdCyc
notation:50 lhs:51 " =C " rhs:51 => eq lhs rhs

theorem eq.refl'{a b x y:Digits}{i j:int}(h0:a =N b)(h1:x = y)(h2:i =I j)(ha:x ≠ ε)(hb:y ≠ ε):⟨a, x, i, ha⟩ =C ⟨b, y, j, hb⟩:=by{
  rw[eq]
  match x, y with | x'::xd, y'::yd => {
    simp[toStdCyc]
    have h'':i.toStdInt = j.toStdInt:=int.eq_iff_toStdInt_eq.mp h2
    rw[h'']
    simp[h1]
    cases Decidable.em (a.toStdNat = ε) with
    | inl h => {
      simp[h]
      have h':b.toStdNat = ε:=by{
        apply Digits.toStdNat.zero_to_nil
        have h:=Digits.toStdNat_ε_isZero h
        exact Digits.nat_eq_zero_isZero h0 h
      }
      simp[h']
    }
    | inr h => {
      simp[h]
      have h':b.toStdNat ≠ ε:=by{
        intro h'
        apply h
        rw[←Digits.isZero_iff_toStdNat_ε] at *
        exact Digits.nat_eq_zero_isZero' h0 h'
      }
      simp[h']
      have h''':a.toStdNat = b.toStdNat:=Digits.nat_eq_iff_toStdNat_eq.mp h0
      simp[h''']
    }
  }
}

theorem eq.refl(x:cyc):x =C x:=
  refl' (Digits.nat.eq.refl _) rfl (int.eq.refl _) x.inv x.inv

theorem eq.symm{x y:cyc}(h:x =C y):y =C x:=
  Eq.symm h

theorem eq.symm_iff{x y:cyc}:x =C y ↔ y =C x:=
  Iff.intro symm symm

theorem eq.trans{x y z:cyc}(h0:x =C y)(h1:y =C z):x =C z:=
  Eq.trans h0 h1

theorem eq.minCyc(a x:Digits)(i:int)(h:x ≠ ε):⟨a, x, i, h⟩ =C ⟨a, x.minCyc, i, Digits.not_ε_minCyc_not_ε h⟩:=by{
  rw[eq]
  match x with
  | x'::d => {
    have h':=Digits.eq_heads_cons_tail (Digits.not_ε_minCyc_not_ε h)
    have h'':(⟨a, (x'::d).minCyc, i, Digits.not_ε_minCyc_not_ε h⟩:cyc) = ⟨a, (Digits.heads (Digits.not_ε_minCyc_not_ε h))::(Digits.tail (Digits.not_ε_minCyc_not_ε h)), i, Digits.noConfusion⟩:=by simp[h']
    rw[h'']
    simp[toStdCyc]
    have h''':(x'::d).minCyc.minCyc = (x'::d).minCyc:=Digits.minCyc.idemp (x'::d)
    simp[h''', h']
  }
}

@[inline] instance instDecidableEq{x y:cyc}:Decidable (x = y):=by{
  match x, y with
  | ⟨x0, x1, x2, _⟩, ⟨y0, y1, y2, _⟩ => {
    simp
    exact instDecidableAnd
  }
}

@[inline] instance eq.instDecidable{x y:cyc}:Decidable (x =C y):=
  instDecidableEq

end cyc
end wkmath
