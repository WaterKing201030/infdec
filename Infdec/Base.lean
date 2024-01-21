theorem Or.comm{p q:Prop}(h:p ∨ q):q ∨ p:=by{
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
}


