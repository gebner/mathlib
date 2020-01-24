import tactic.hammer.feature_search system.io tactic.core meta.coinductive_predicates tactic.derive_to_string

meta def format.paren' (a : format) :=
a.paren.group

meta def expr.constants (e : expr) : list name :=
native.rb_set.to_list $ e.fold native.mk_rb_set $ λ e _ s,
match e with
| (expr.const n _) := s.insert n
| _ := s
end

namespace hammer

@[derive decidable_eq, derive has_to_string, derive has_repr]
def lbool := option bool

namespace lbool

@[pattern] def ff : lbool := some ff
@[pattern] def tt : lbool := some tt
@[pattern] def undef : lbool := none

def not (a : lbool) : lbool :=
bnot <$> a

def and (a b : lbool) : lbool :=
band <$> a <*> b

def or (a b : lbool) : lbool :=
bor <$> a <*> b

def imp (a b : lbool) : lbool :=
a.not.or b

def iff (a b : lbool) : lbool :=
(λ a b : bool, (a ↔ b : bool)) <$> a <*> b

end lbool

open tactic expr native

inductive fo_term
| fn (sym : name) (args : list fo_term)
| var (sym : name)

namespace fo_term

protected meta def to_fmt : fo_term → format
| (fn s []) := _root_.to_fmt s
| (fn s as) := _root_.to_fmt s ++
  (format.paren' $ format.join $
    list.intersperse ("," ++ format.line) $ as.map to_fmt)
| (var s) := _root_.to_fmt s

meta instance : has_to_tactic_format fo_term := ⟨pure ∘ fo_term.to_fmt⟩
meta instance : has_to_format fo_term := ⟨fo_term.to_fmt⟩
meta instance : has_to_string fo_term := ⟨to_string ∘ to_fmt⟩
meta instance : has_repr fo_term := ⟨to_string ∘ to_fmt⟩

end fo_term

def fo_term.const (sym : name) : fo_term :=
fo_term.fn sym []

inductive fo_fml
| eq (a b : fo_term)
| pred (sym : name) (args : list fo_term)
| true | false
| neg (a : fo_fml)
| and (a b : fo_fml)
| or (a b : fo_fml)
| imp (a b : fo_fml)
| iff (a b : fo_fml)
| all (x : name) (a : fo_fml)
| ex (x : name) (a : fo_fml)

namespace fo_fml

def alls : list name → fo_fml → fo_fml
| (x :: xs) a := all x (alls xs a)
| [] a := a

private meta def binop (op : string) (a : format) (b : format) : format :=
format.paren' $ a ++ format.space ++ op ++ format.line ++ b

private meta def quant (q : string) (x : name) (b : format) : format :=
format.paren' $ q ++ format.space ++ _root_.to_fmt x ++ "," ++ format.line ++ b

protected meta def to_fmt : fo_fml → format
| (eq a b) := binop "=" a.to_fmt b.to_fmt
| true := "⊤"
| false := "⊥"
| (neg a) := format.paren' $ "¬" ++ format.line ++ a.to_fmt
| (and a b) := binop "∧" a.to_fmt b.to_fmt
| (or a b) := binop "∨" a.to_fmt b.to_fmt
| (imp a b) := binop "→" a.to_fmt b.to_fmt
| (iff a b) := binop "↔" a.to_fmt b.to_fmt
| (all x a) := quant "∀" x a.to_fmt
| (ex x a) := quant "∃" x a.to_fmt
| (pred s as) := (fo_term.fn s as).to_fmt

meta instance : has_to_tactic_format fo_fml := ⟨pure ∘ fo_fml.to_fmt⟩
meta instance : has_to_format fo_fml := ⟨fo_fml.to_fmt⟩
meta instance : has_to_string fo_fml := ⟨to_string ∘ to_fmt⟩
meta instance : has_repr fo_fml := ⟨to_string ∘ to_fmt⟩

def approx : fo_fml → lbool
| false := lbool.ff
| true := lbool.tt
| (eq a b) := lbool.undef
| (pred _ _) := lbool.undef
| (neg a) := a.approx.not
| (imp a b) := a.approx.imp b.approx
| (or a b) := a.approx.or b.approx
| (and a b) := a.approx.and b.approx
| (ex x a) := a.approx
| (all x a) := a.approx
| (iff a b) := a.approx.iff b.approx

def is_trivially_true (a : fo_fml) : bool :=
a.approx = lbool.tt

end fo_fml

def term_prf := fo_term.const ``true.intro

def tptpify_char : char → list char | c :=
if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9') then [c] else
match c with
| 'α' := ['_', 'g', 'a']
| 'β' := ['_', 'g', 'b']
| '₁' := ['_', 'l', '1']
| '₂' := ['_', 'l', '2']
| '_' := ['_', '_']
| '\'' := ['_', 'p']
| c := '_' :: 'u' ::
  (list.range 6).reverse.map (λ i, (c.val / 16^i % 16).digit_char)
end

def tptpify_string (s : string) : string :=
(s.to_list >>= tptpify_char).as_string

meta def tptpify_name : name → string
| name.anonymous := ""
| (name.mk_string s name.anonymous) := tptpify_string s
| (name.mk_numeral i name.anonymous) := to_string i
| (name.mk_string s n) := tptpify_name n ++ "_o_" ++ tptpify_string s
| (name.mk_numeral s n) := tptpify_name n ++ "_n" ++ to_string s

meta def fn_tptpify_name : name → string
| `_T := "t"
| `_S := "s"
| `_A := "a"
| `_P := "p"
| n := "c" ++ tptpify_name n

meta def var_tptpify_name (n : name) : string :=
"X" ++ tptpify_name n

meta def ax_tptpify_name (n : name) : string :=
fn_tptpify_name n

meta def tptpify_term : fo_term → format
| (fo_term.fn s []) := fn_tptpify_name s
| (fo_term.fn s as) := format.group $ fn_tptpify_name s ++
  format.paren (format.join $ list.intersperse ("," ++ format.line) $ as.map tptpify_term)
| (fo_term.var s) := var_tptpify_name s

meta def tptpify_binop (op : string) (a : format) (b : format) : format :=
format.paren' $ a ++ format.space ++ op ++ format.line ++ b

meta def tptpify_quant (q : string) (x : name) (b : format) : format :=
format.paren' $ q ++ "[" ++ var_tptpify_name x ++ "]:" ++ format.line ++ b

section open fo_fml
meta def tptpify_fml : fo_fml → format
| (eq a b) := tptpify_binop "=" (tptpify_term a) (tptpify_term b)
| true := "$true"
| false := "$false"
| (neg a) := format.paren' $ "~" ++ format.line ++ (tptpify_fml a)
| (and a b) := tptpify_binop "&" (tptpify_fml a) (tptpify_fml b)
| (or a b) := tptpify_binop "|" (tptpify_fml a) (tptpify_fml b)
| (imp a b) := tptpify_binop "=>" (tptpify_fml a) (tptpify_fml b)
| (iff a b) := tptpify_binop "<=>" (tptpify_fml a) (tptpify_fml b)
| (all x a) := tptpify_quant "!" x (tptpify_fml a)
| (ex x a) := tptpify_quant "?" x (tptpify_fml a)
| (pred s as) := tptpify_term (fo_term.fn s as)
end

meta def tptpify_ann (role : string) (n : name) (f : fo_fml) : format :=
format.group $ format.nest 1 $ "fof(" ++ format.group (
    ax_tptpify_name n ++ "," ++ format.line ++ role ++ ",")
  ++ format.line ++ tptpify_fml f ++ ")."

end hammer
