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

def movl{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int):cyc:=
  if h:(Digits.heads hn) = ε then
    if (Digits.tail hn) = (0) then
      ⟨ε, ε::(0), int.Zero, Digits.noConfusion⟩
    else
    ⟨ε, x, e, hn⟩
  else if h':Digits.head hn = (0) then
    have hc':x.rotl.minCyc = x.rotl:=Digits.minCyc_rotl_minCyc hc
    have hn':x.rotl ≠ ε:=by{
      intro tmp
      have tmp:=Digits.rotl_cancel (tmp.trans (rfl:ε = (ε).rotl):_ = (ε).rotl)
      exact hn tmp
    }
    have : Digits.headzerocountLt (x.rotl) x:=by{
      have : x.rotl.headzerocount.Succ =N x.headzerocount:=by{
        simp[Digits.rotl] at *
        apply Digits.nat.eq.symm
        rw[Digits.headzerocount]
        simp[hn,h']
        rw[Digits.Succ, Digits.Succ]
        apply λ h => Digits.nat.eq_of_eq_add_eq h (Digits.nat.eq.refl Digits.One)
        have tmp : ¬(Digits.tails hn).isZero:=by {
          match x with | x'::d' => {
            simp[Digits.heads] at h
            simp at hc'
            intro hf
            have tmp : ¬ x'.isZero:=by{
              rw[←Digits.tails.cons_tails h] at hf
              rw[Digits.isZero] at hf
              simp[hf.right] at *
              rw[Digits.tails.cons_tails Digits.noConfusion] at hc'
              have h'':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)).isZero:=by{
                rw[←Digits.tails.cons_tails]
                rw[←Digits.tails.cons_tails h]
                simp[Digits.isZero]
                exact hf
              }
              rw[h'] at hc'
              have h''':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε ∨ (Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε::(0) := Digits.isZero_minCyc_eq_self h'' hc'
              rw[←Digits.tails.cons_tails Digits.noConfusion] at h'''
              simp at h'''
              rw[←Digits.tails.cons_tails h] at h'''
              contradiction
            }
            apply tmp
            have h':Digits.head h = (0):=by{
              rw[Digits.head.cons_head]
              exact h'
            }
            have h'':=Digits.eq_head_append_tails h
            rw[←h'', h']
            have h':(ε::(0)).isZero:=by simp
            rw[←Digits.tails.cons_tails h] at hf
            rw[Digits.isZero] at hf
            exact Digits.zero_append_zero_isZero h' hf.left
          }
        }
        rw[Digits.notZero_cons_zero_headzerocount_eq tmp]
        exact Digits.nat.eq.refl _
      }
      exact Digits.nat.lt_iff_Succ_le.mpr this.to_le
    }
    movl hn' hc' (e - int.One).toStdInt
  else
    ⟨ε, x, e, hn⟩
termination_by' {
  rel:=λ x y:(_:Digits) ×' _ => Digits.headzerocountLt x.fst y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.headzerocountLt.wf
}

-- 这个得改成movl一样的参数
def movr{n x:Digits}(h0:n.isStdNat)(h1:n ≠ ε)(h2:x ≠ ε)(e:int):cyc:=
  if (Digits.tail h1) = (Digits.tail h2) then
    if h:(Digits.heads h1) = ε then
      ⟨ε, x.rotr, e + int.One, by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[h2];exact Digits.not_ε_append Digits.noConfusion _}⟩
    else
      have h':x.rotr ≠ ε:=by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[h2];exact Digits.not_ε_append Digits.noConfusion _}
      have : (Digits.heads h1) <L n:=by{
        match n with
        | _::_ => simp[Digits.heads]; exact Digits.len.lt_cons _ _
      }
      movr (Digits.isStdNat_heads_isStdNat h1 h0) h h' (e + int.One).toStdInt
  else
    ⟨n, x, e, h2⟩
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.len.lt.wf
}

def toStdCyc(c:cyc):cyc:=
  match c with
  | ⟨n, x, e, h⟩ =>
    have hn: x.minCyc ≠ ε := Digits.not_ε_minCyc_not_ε h
    have hc: (x.minCyc).minCyc = x.minCyc := Digits.minCyc.idemp x
    if h':n.toStdNat = ε then
      movl hn hc e.toStdInt
    else
      movr (Digits.toStdNat_isStdNat n) h' hn e.toStdInt

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

theorem eq.movr_eq(a:Digits)(d:Digit)(x:Digits)(i:int):⟨a::d, x::d, i, Digits.noConfusion⟩ =C ⟨a, (ε::d)++x, i + int.One, Digits.not_ε_append Digits.noConfusion x⟩:=by{
  rw[eq]
  have h':=Digits.eq_heads_cons_tail (Digits.not_ε_append (Digits.noConfusion:ε::d ≠ ε) x)
  have h'':(⟨a, ε::d ++ x, i + int.One, Digits.not_ε_append Digits.noConfusion x⟩:cyc) = ⟨a, (Digits.heads (Digits.not_ε_append (Digits.noConfusion:ε::d ≠ ε) x))::(Digits.tail (Digits.not_ε_append (Digits.noConfusion:ε::d ≠ ε) x)), i + int.One, Digits.noConfusion⟩:=by simp[h']
  rw[h'']
  simp[toStdCyc]
  cases Decidable.em (a.toStdNat = ε) with
  | inl h => {
    simp[h]
    match d with
    | (0) => {
      have h''':(a::(0)).toStdNat = ε:=by{
        rw[←Digits.isZero_iff_toStdNat_ε]
        simp[Digits.isZero]
        exact Digits.isZero_iff_toStdNat_ε.mpr h
      }
      simp[h''', h']
      rw[movl]
      cases Decidable.em (Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.noConfusion:x::(0) ≠ ε)) = ε) with
      | inl h0 => {
        simp[h0]
        have h1:x.isZero:=by{
          have hc:(x::(0)).minCyc ≠ ε:=Digits.not_ε_minCyc_not_ε (Digits.noConfusion:x::(0) ≠ ε)
          match hc':(x::(0)).minCyc with
          | ε => contradiction
          | y::yd => {
            have hc'':(y::yd).isPostfixOf (x::(0)):=by{
              apply Digits.isCycParent_isPostfixOf
              rw[←hc']
              exact Digits.isCycParent_minCyc _
            }
            rw[Digits.isPostfixOf] at hc''
            simp[hc'] at h0
            simp[Digits.heads] at h0
            rw[h0, hc''.left] at hc'
            have hc'':(ε::(0)).isZero:=by simp
            have hc''':(x::(0)).isCycParent (Digits.minCyc (x::(0))):=Digits.isCycParent_minCyc _
            rw[←hc'] at hc''
            have hc''':=Digits.isCycParent_zero_isZero hc'' hc'''
            rw[Digits.isZero] at hc'''
            exact hc'''.left
          }
        }
        have h2:ε::(0) ++ x = x::(0):=by{
          rw[←Digits.append_tail x]
          have h2:(ε::(0)).isZero:=by simp
          exact Digits.zero_append_zero_comm h2 h1
        }
        simp[h2]
        rw[movl]
        have h3:(x::(0)).minCyc = ε::(0):=by{
          apply Digits.not_ε_isZero_minCyc Digits.noConfusion
          simp[Digits.isZero]
          exact h1
        }
        simp[h0]
        simp[h3]
        simp[Digits.tail]
      }
      | inr h0 => {
        simp[h0, Digits.eq_heads_cons_tail]
        cases Decidable.em (Digits.head (_:Digits.minCyc (x::(0)) ≠ ε) = (0)) with
        | inl h1 => {
          simp[h1]
          apply Eq.symm
          rw[movl]
          have h2:Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append Digits.noConfusion x):((ε::(0))++x).minCyc ≠ ε) ≠ ε:=by{
            intro h2
            apply h0
            apply Digits.len.ε_unique
            rw[←congrArg (λ x => Digits.heads _ =L x) h2]
            apply Digits.heads_len_cancel
            have h3:ε::(0) ++ x = (x::(0)).rotr:=by simp[Digits.rotr]
            rw[h3]
            rw[←Digits.rotr_minCyc_comm]
            exact (Digits.rotr_len_eq _).symm
          }
          simp[h2]
          simp[Digits.eq_heads_cons_tail]
          simp[Digits.minCyc_head_eq_head (Digits.not_ε_append Digits.noConfusion x:ε::(0) ++ x ≠ ε)]
          simp[Digits.head_of_head_append_tails]
          rw[movl]
          have h3:Digits.tails (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append Digits.noConfusion x):(ε::(0)++x).minCyc ≠ ε) ≠ ε :=by{
          }
          simp[h3]

        }
        | inr h1 => {
          simp[h1]
          rw[movl]

        }
      }
    }
    | (1)
    | (2) => {

    }
  }
  | inr h => {
    simp[h]
    have h':(a::d).toStdNat ≠ ε:=by{
      intro h'
      apply h
      rw[←Digits.isZero_iff_toStdNat_ε] at *
      rw[Digits.isZero] at h'
      exact h'.left
    }
    simp[h']
  }
}

theorem eq.movl{d:Digit}{a x:Digits}{i:int}:⟨a::d, x::d, i - int.One, Digits.noConfusion⟩ =C ⟨a, (ε::d)++x, i, Digits.not_ε_append Digits.noConfusion x⟩:=by{
  apply movr.trans
  apply refl' (Digits.nat.eq.refl _) (Eq.refl _)
  rw[int.sub]
  apply (int.add.assoc _ _ _).trans
  have h'':(-int.One + int.One).isZero:=by simp[int.One, int.neg, int.add, Digits.sub, Digits.half_sub, Digits.half_sub', Digit.half_sub3, int.isZero]
  exact int.add_zero i h''
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
