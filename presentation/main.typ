#import "@preview/diatypst:0.5.0": *
#import "@preview/zebraw:0.5.5": *
#import "@preview/curryst:0.5.1": rule, prooftree
#import "@preview/cetz:0.4.2"
#import "makros.typ": *

#show: slides.with(
  title: $pi"FD" - "A Process Calculus for Parigot's Free Deduction"$, // Required
  subtitle: "Formalizing the Metatheory of Elimination-Based Concurrency in Rocq",
  date: "20.03.2026",
  authors: ("Filip Šimić"),
  // Optional Style Options
  title-color: karminrot.darken(70%),
  ratio: 16/9,
  layout: "medium", // one of "small", "medium", "large"
  toc: false,
  count: none, // one of "dot", "number", or none
  footer: false,
  // footer-title: "Custom Title",
  // footer-subtitle: "",
  // theme: "full", // one of "normal", "full"
)

#set heading(numbering: none)

==
#box(
  width: 100%,
  height: 20.5cm, // Adjust height to cut off right after the authors/abstract
  clip: true,
  stroke: 0.0pt + black,
  image("paper/parigot-freededuction.pdf", page: 1, width: 100%)
)
#hide[#cite(label("parigot:1991:free-deduction"), form: none)]

= Around Introduction And Elimination
==
#box(
  width: 100%,
  height: 20cm, // Adjust height to cut off right after the authors/abstract
  clip: true,
  stroke: 0.0pt + black,
  image("paper/ostermann-introelim.pdf", page: 2, width: 100%)
)
#hide[#cite(label("ostermann:2022:intro-elim"), form: none)]

==
#align(horizon)[
#grid(
  columns: (1fr, 1fr),
  align: (center, center),
  row-gutter: 4em,
  [#prooftree(
    rule(
      name: $"L" dot.o "Intro"$,
      $Gamma, dot.o(T_1, dots.h.c, T_n) tack.r Delta$,
      $P_1 med med dots.h.c med med P_k$
    )
  )],
  [#prooftree(
    rule(
      name: $"R" dot.o "Intro"$,
      $Gamma tack.r dot.o(T_1, dots.h.c, T_n), Delta$,
      $P_1 med med dots.h.c med med P_k$
    )
  )],
  [#prooftree(
    rule(
      name: $"L" dot.o "Elim"$,
      $C$,
      $Gamma, dot.o(T_1, dots.h.c, T_n) tack.r Delta$,
      $P_1 med med dots.h.c med med P_k$
    )
  )],
  [#prooftree(
    rule(
      name: $"R" dot.o "Elim"$,
      $C$,
      $Gamma tack.r dot.o(T_1, dots.h.c, T_n), Delta$,
      $P_1 med med dots.h.c med med P_k$
    )
  )],
)]

==
Consider the sequent
#v(1em)
$
  tack.r (A and B) arrow.r (B and A)
$
#v(1em)

#grid(
  columns: (1fr, 1fr),
  align: (center + horizon, center + horizon),
  row-gutter: 3em,
  [*Natural Deduction*],
  [*Gentzen's LK*],
  [#prooftree(
    rule(
      name: $"R"arrow.r"Intro"$,
      $tack.r (A and B) arrow.r (B and A)$,
      rule(
        name: $"R"and"Intro"$,
        $A and B tack.r B and A$,
        rule(
          name: $"R"and"Elim"_2$,
          $A and B tack.r B$,
          rule(
            name: "Ax",
            $A and B tack.r A and B$
          )
        ),
        rule(
          name: $"R"and"Elim"_1$,
          $A and B tack.r A$,
          rule(
            name: "Ax",
            $A and B tack.r A and B$
          )
        )
      )
    )
  )],
  [#prooftree(
      rule(
        name: $"R"arrow.r"Intro"$,
        $tack.r (A and B) arrow.r (B and A)$,
        rule(
          name: $"L"and"Intro"$,
          $A and B tack.r B and A$,
          rule(
            name: $"R"and"Intro"$,
            $A, B tack.r B and A$,
            rule(
              name: "Ax",
              $A, B tack.r B$
            ),
            rule(
              name: "Ax",
              $A, B tack.r A$
            )
          )
        )
      )
  )]
)

== A Free Deduction Proof
#align(horizon)[
$
  #prooftree(
    rule(
      name: $"L"arrow.r"E"$,
      $tack.r (A and B) arrow.r (B and A)$,
      rule(
        name: "Ax",
        $(A and B) arrow.r (B and A) tack.r (A and B) arrow.r (B and A)$
      ),
      rule(
        name: $"R"and"E"$,
        $A and B tack.r B and A$,
        rule(
          name: "Ax",
          $A and B tack.r A and B$
        ),
        rule(
          name: $"L"and"E"_1$,
          $A, B tack.r B and A$,
          rule(
            name: "Ax",
            $B and A tack.r B and A$
          ),
          rule(
            name: "Ax",
            $A tack.r A$
          )
        )
      )
    )
  )
$]
\ \
#align(center + horizon)[
  #hide[*What do elimination rules have to do with communication?*]
]

== A Free Deduction Proof
#align(horizon)[
$
  #prooftree(
    rule(
      name: $"L"arrow.r"E"$,
      $tack.r (A and B) arrow.r (B and A)$,
      rule(
        name: "Ax",
        $(A and B) arrow.r (B and A) tack.r (A and B) arrow.r (B and A)$
      ),
      rule(
        name: $"R"and"E"$,
        $A and B tack.r B and A$,
        rule(
          name: "Ax",
          $A and B tack.r A and B$
        ),
        rule(
          name: $"L"and"E"_1$,
          $A, B tack.r B and A$,
          rule(
            name: "Ax",
            $B and A tack.r B and A$
          ),
          rule(
            name: "Ax",
            $A tack.r A$
          )
        )
      )
    )
  )
$]
\ \
#align(center + horizon)[
  *What do elimination rules have to do with communication?*
]

== Example: Ephemeral Booleans
#zebraw(
    numbering-separator: true,
    lang: false,
    ```haskell
    type 𝔹 = 1 ⊕ 1
    type co𝔹 = ⊥ & ⊥
    type ServerProtocol = co𝔹 ⅋ 𝔹
    type ClientProtocol = 𝔹 ⊗ co𝔹

    true  = ◁ inl (z . z ⟷ ![])
    false = ◁ inr (z . z ⟷ ![])

    client : ClientProtocol ⊢ negation
    negation =
      (client : ClientProtocol) ⟷ (server : ServerProtocol);
       server ? (b, c) . b ⟷ ▷ {
         z . z ⟷ ?() . (c ⟷ false),
         z . z ⟷ ?() . (c ⟷ true)
       }
    ```
)

== From Free Deduction to $pi$FD
#box(
  width: 100%,
  height: 20.5cm, // Adjust height to cut off right after the authors/abstract
  clip: true,
  stroke: 0.0pt + black,
  image("paper/parigot-freededuction.pdf", page: 3, width: 100%)
)

== Types
#align(horizon)[
#definition(title: "Types")[
  $ T ::= & A times.o B && quad "output A, then behave as B" \
        | & A amp.inv B      && quad "input A, then behave as B" \
        | & A plus.o B  && quad "select from A or B" \
        | & A with B         && quad "offer choice of A or B" \
        | & 1                && quad "close" \
        | & bot              && quad "wait" $
]
#definition(title: $"Linear Negation" (dot)^perp$)[
  #grid(
    columns: (1fr, 2fr, 2fr, 1fr),
    align: (center, center),
    [],
    [
      $
        1^perp &:= bot \
        (A times.o B)^perp &:= A^perp amp.inv B^perp \
        (A plus.o B)^perp &:=  A^perp amp B^perp
      $
    ],
    [
      $
        bot^perp &:= 1 \
        (A amp.inv B)^perp &:= A^perp times.o B^perp \
        (A amp B)^perp &:=  A^perp times.o B^perp
      $
    ],
    []
  )
]
]

== From Free Deduction to $pi$FD
// #let hl(content) = box(
//   content,
//   inset: 0.1em,
//   fill: mattgold,
// )
#let hl(content) = box(
  fill: mattgold,
  inset: (x: 0.3em, y: 0.2em), // "x" for horizontal, "y" for vertical padding
  outset: (y: 0.1em),          // Prevents the highlight from making the line "jump"
  radius: 2pt,
  baseline: 20%,              // Adjusts the highlight so it sits better on the math baseline
  content
)

#align(horizon)[
$
  #prooftree(
    rule(
      name: $$,
      $Gamma_1, Gamma_2, Gamma_3 tack.r Delta_1, Delta_2, Delta_3$,
      $Gamma_1, A times.o B tack.r Delta_1$,
      $Gamma_2 tack.r A, Delta_2$,
      $Gamma_3 tack.r B, Delta_3$
    )
  ) quad #sym.arrow.r.squiggly quad
  #prooftree(
    rule(
      name: $$,
      $Pi_1, Pi_2, Pi_3 tack.r $,
      $Pi_1, A times.o B tack.r $,
      $Pi_2, A^perp tack.r $,
      $Pi_3, B^perp tack.r$
    )
  )
$
]

==
#align(horizon)[
$
  #prooftree(
    rule(
      name: $"T-"times.o$,
      [$Gamma_1, Gamma_2, Gamma_3 tack.r $ #hl[$P; med x![v.Q | z.R]$]],
      [$Gamma_1,$ #hl[$x :$] $A times.o B tack.r$ #hl[$P$]],
      [$Gamma_2,$ #hl[$v :$] $A^perp tack.r$ #hl[$Q$]],
      [$Gamma_3,$ #hl[$z :$] $B^perp tack.r$ #hl[$R$]]
    )
  )
$
]
\ 
#align(center + horizon)[
  #table(
    columns: (auto, auto),
    align: left,
    table.header(
      [Term Assignment], [Interpretation],
    ),
    $P$,
    [A process with an unfulfilled promise $x$ adhering to protocol $A times.o B$],
    $v.Q$,
    [A process outputting a message of type $A$ along $v$],
    $z.R$,
    [A continuation process where channel $z$ handles session protocol $B$],
    [$"T-"times.o$],
    [Fulfills a promise of type $A times.o B$ with the secondary premises as payload]
  )
]

==
#align(horizon)[
$
  #prooftree(
    rule(
      name: $"T-"times.o$,
      $Gamma_1, Gamma_2, Gamma_3 tack.r P; med x![v.Q | z.R]$,
      $Gamma_1, x : A times.o B tack.r P$,
      [#hl[$Gamma_2, v : A^perp tack.r Q
       quad Gamma_3, z : B^perp tack.r R$]]
    )
  ) \ \ \ \ quad #sym.arrow.r.squiggly quad
  #prooftree(
    rule(
      name: $"T-Seq"$,
      $Gamma_1, Gamma_2, Gamma_3 tack.r P; med x![v.Q | z.R]$,
      $Gamma_1, x : A times.o B tack.r P$,
      rule(
        name: [#hl[$times.o"-Intro"$]],
        $Gamma_2, Gamma_3 tack.r ![v.Q | z.R] : A times.o B$,
        $Gamma_2, v : A^perp tack.r Q$,
        $Gamma_3, z : B^perp tack.r R$
      )
    )
  )
$
]

==
#box(
  width: 100%,
  height: 19cm, // Adjust height to cut off right after the authors/abstract
  clip: true,
  stroke: 0.0pt + black,
  image("paper/negri-ucl.pdf", page: 1, width: 100%)
)
#hide[#cite(label("negri:2002:var-linlog"), form: none)]

==
\
$
  #prooftree(
    rule(
      name: $$,
      $Gamma tack.r A times.o B, Delta$,
      $Gamma tack.r A, Delta$,
      $Gamma tack.r B, Delta$
    )
  )
$
\
#grid(
  columns: (1fr, 1fr),
  align: (center, center),
  row-gutter: 2em,
  [*Inversion Principle*],
  [*Dual Inversion Principle*],
  [_"Whatever follows from the grounds for deriving a formula must follow from that formula."_],
  [_"Whatever follows from a formula must follow from the sufficient grounds for deriving the formula."_],
  [
    #prooftree(
      rule(
        name: $$,
        $Gamma tack.r Delta$,
        $Gamma tack.r A times.o B, Delta$,
        $Gamma, A, B tack.r Delta$
      )
    )
  ],
  [
    #prooftree(
      rule(
        name: $$,
        $Gamma tack.r Delta$,
        $Gamma, A times.o B tack.r Delta$,
        $Gamma tack.r A, Delta$,
        $Gamma tack.r B, Delta$
      )
    )
  ]
)

== Syntax of $pi$FD
\
#definition(title: "Syntax")[
  #v(0.3cm)
  #grid(
    columns: (1fr, auto, 1fr),
    align: (center, center),
    [
      $
        &"Process" in.rev P, Q &::=
           & M arrow.l.r M
          && quad "link" \
        &&|& (nu x y) (P | Q)
          && quad "cut" \
        &&|& P; med x S
          && quad "sequencing" \
        &&|& "stop"
          && quad "nil process" \
        \
        &"Message" in.rev M &::=
           & x
          && quad "future" \
        &&|& S
          && quad "statement" \
      $
    ],
    line(angle: 90deg, length: 11em, stroke: 0.5pt + black),
    [
      $
        &"Statement" in.rev S &::=
           & med lt.tri "inl"(x.P)
          && quad "selection" \
        &&|& med lt.tri "inr"(x.P)
          && quad "selection" \
        &&|& med gt.tri {x.P, x.P}
          && quad "choice" \
        &&|& med ![x.P | x.P]
          && quad "output" \
        &&|& med ?(x, x).P
          && quad "input" \
        &&|& med ![]
          && quad "close" \
        &&|& med ?().P
          && quad "wait"
      $
    ]
  )
  #v(0.2cm)
]

==
#grid(
  columns: (1fr, auto, 1fr),
  align:   (center, center, center),
  gutter: 1em,
  [#rect[$Gamma tack.r P$]],
  [],
  [#rect[$Gamma tack.r M : A$]],
  [
    \
    #prooftree(
      rule(
        name: "T-Ax",
        $Gamma, Gamma' tack.r M_1 arrow.l.r M_2$,
        $Gamma tack.r M_1 : A$,
        $Gamma' tack.r M_2 : A^perp$
      )
    )
    \
    #prooftree(
      rule(
        name: "T-Cut",
        $Gamma, Gamma' tack.r (nu x y)(P | Q)$,
        $Gamma, x : A tack.r P$,
        $Gamma', y : A^perp tack.r Q$
      )
    )
    \
    #prooftree(
      rule(
        name: "T-Seq",
        $Gamma, Gamma' tack.r P; med x S$,
        $Gamma, x : A tack.r P$,
        $Gamma' tack.r S : A$
      )
    )
  ],
  line(angle: 90deg, length: 17em, stroke: 0.5pt + black),
  [
    \
    #prooftree(
      rule(
        name: "T-Id",
        $x : A tack.r x : A$
      )
    )

    #prooftree(
      rule(
        name: $"T-"plus.o_1$,
        $Gamma tack.r med lt.tri"inl"(z.Q) : A plus.o B$,
        $Gamma, z : A^perp tack.r Q$
      )
    )

    #prooftree(
      rule(
        name: $"T-"amp$,
        $Gamma tack.r med gt.tri {z_1.Q_1, z_2.Q_2} : A amp B$,
        $Gamma, z_1 : A^perp tack.r Q_1$,
        $Gamma, z_2 : B^perp tack.r Q_2$
      )
    )

    #prooftree(
      rule(
        name: $"T-"amp.inv$,
        $Gamma tack.r med ?(v, z).Q : A amp.inv B$,
        $Gamma, v : A^perp, z : B^perp tack.r Q$
      )
    )

    #sym.dots.v
  ],
)

== $pi$FD and Linear System L
#align(horizon + center)[
  #table(
    columns: (auto, auto),
    align: left,
    table.header(
      [$pi"FD"$], [$"Linear" L$],
    ),
    [$M_1 arrow.l.r M_2$],
    [$chevron.l M_1 | M_2 chevron.r$],
    [$P; med x M$],
    [$chevron.l mu x . P | M chevron.r$],
    [$(nu x y)(P | Q)$],
    [$chevron.l mu x.P | mu y.Q chevron.r$]
  )
]

== $pi$FD and Linear System L
#align(horizon + center)[
  #table(
    columns: (auto, auto),
    align: left,
    table.header(
      [$pi"FD"$], [$"Linear" L$],
    ),
    [$M_1 arrow.l.r M_2$],
    [$chevron.l M_1 | M_2 chevron.r$],
    [$P; med x M$],
    [$chevron.l mu x . P | M chevron.r$],
    [$(nu x y)(P | Q)$],
    [$chevron.l mu x.P | mu y.Q chevron.r$]
  )
]
#example(title: [Non-confluence of linearly typed L terms (#cite(label("spiwack:2016:dissection-of-l"), form: "prose"))])[
The $L$ term
$
  chevron.l
  mu x . chevron.l (x, z) | v chevron.r
  |
  mu y . chevron.l (t, y) | w chevron.r
  chevron.r
$
may reduce non-deterministically but can be translated to the $pi$FD normalform
$
  (nu x y)( bracket.l.stroked (x, z) bracket.r.stroked arrow.l.r v |
            bracket.l.stroked (t, y) bracket.r.stroked arrow.l.r w )
$
where $bracket.l.stroked (x, z) bracket.r.stroked := ![x'.x arrow.l.r x' | z'.z arrow.l.r z']$. \
Normalforms in Free Deduction may contain cuts. However, these cuts do not violate the subformula property.
]

= Structural Congruence
== Structural Congruence
#align(horizon)[
#definition(title: $"Structural Congruence" equiv$)[
  $equiv$ is defined as the least congruence relation that is closed under the following axioms:
  #grid(
    columns: (1fr, auto), // Left column takes all space, right column fits the name
    row-gutter: 1.5em,
    align: (center, right + horizon),
    [$ M_1 arrow.l.r M_2 &equiv M_2 arrow.l.r M_1 $],
    [(C-Link)],
    [$ (nu x y)(P | Q) equiv (nu y x)(Q | P) $],
    [(C-Comm)],
    [#prooftree(
      vertical-spacing: 3pt,
      rule(
        name: "",
        $(nu v z)((nu x y)(P | Q)| R) equiv (nu x y)(P | (nu v z)(Q | R))$,
        $v in.not "FV"(P) "and" y in.not "FV"(R)$
      )
    )],
    [(C-Assoc)]
  )
]

#lemma(title: $"Preservation of Types under Structural Congruence"$,
       mechanized: true)[
  #set enum(numbering: "(i)")
  If $P equiv Q$, then $Gamma tack.r P$ iff $Gamma tack.r Q$.
]
]

= Reduction
== Logical Redexes
#align(horizon)[
$
  #prooftree(
    rule(
      name: "R-Elim",
      $Gamma_1, Gamma_2 tack.r Delta_1, Delta_2$,
      rule(
        name: "L-Elim",
        $Gamma_1 tack.r A, Delta_1$,
        rule(
          name: "Ax",
          $A tack.r A$
        ),
        $#sym.dots.h.c$
      ),
      $#sym.dots.h.c$
    )
  )
  quad quad "or" quad quad
  #prooftree(
    rule(
      name: "L-Elim",
      $Gamma_1, Gamma_2 tack.r Delta_1, Delta_2$,
      rule(
        name: "R-Elim",
        $Gamma_1, A tack.r Delta_1$,
        rule(
          name: "Ax",
          $A tack.r A$
        ),
        $#sym.dots.h.c$
      ),
      $#sym.dots.h.c$
    )
  )
$
]

== Logical Redex: Choice and Selection
#align(horizon)[
$
  #prooftree(
    rule(
      name: $amp"Elim"$,
      [$Gamma, Delta tack.r$ #hl[$x arrow.l.r y; med x lt.tri"inl"(z.Q); med y gt.tri{z_1.Q_1, z_2.Q_2}$]],
      rule(
        name: $plus.o"Elim"$,
        [$Gamma, y : A^perp amp B^perp tack.r$ #hl[$x arrow.l.r y; med x lt.tri"inl"(z.Q)$]],
        rule(
          name: "T-Ax",
          [$x : A times.o B, y : A^perp amp B^perp tack.r$ #hl[$x arrow.l.r y$]]
        ),
        [$Gamma, z : A^perp tack.r$ $Q$]
      ),
      [$Delta, z_1: A tack.r$ $Q_1$ \ $Delta, z_2: A tack.r$ $Q_2$]
    )
  ) \ \ \ \
  gt.tri quad quad 
  #prooftree(
    rule(
      name: "T-Cut",
      [$Gamma, Delta tack.r$ #hl[$(nu z z_1)(Q | Q_1)$]],
      $Gamma, z : A^perp tack.r Q$,
      $Delta, z_1 : A tack.r Q_1$
    )
  )
$
]

== Structural Redexes
#align(horizon)[
  $
    #prooftree(
      rule(
        name: $"L"dot.o"Elim"$,
        $Gamma_1, dots.h, Gamma_n, Gamma' tack.r Delta_1, dots.h, Delta_n, Delta'$,
        rule(
          name: $R$,
          $Gamma_1, dots.h, Gamma_n, dot.o(overline(T_j)) tack.r Delta_1, dots.h, Delta_n$,
          $P_1 quad dots.h.c quad attach(P, br: i - 1)$,
          $Gamma_i, dot.o(overline(T_j)) tack.r Delta_i$,
          $attach(P, br: i + 1) quad dots.h.c quad P_n$
        ),
        $P'_1 quad dots.h.c quad P'_n$
      )
    ) \ \ \ \
    gt.tri quad quad
    #prooftree(
      rule(
        name: $R$,
        $Gamma_1, dots.h, Gamma_n, Gamma' tack.r Delta_1, dots.h, Delta_n, Delta'$,
        $P_1 quad dots.h.c quad attach(P, br: i - 1)$,
        rule(
          name: $"L"dot.o"Elim"$,
          $Gamma_i, Gamma' tack.r Delta_i, Delta'$,
          $Gamma_i, dot.o(overline(T_j)) tack.r Delta_i$,
          $P'_1 quad dots.h.c quad P'_n$
        ),
        $attach(P, br: i + 1) quad dots.h.c quad P_n$
      )
    )
  $
]

== Contraction
#align(horizon)[
#grid(
    columns: (1fr, auto), // Left column takes all space, right column fits the name
    row-gutter: 1.5em,
    align: (center, right + horizon),
    [$ ![v.P | z.Q] med med arrow.l.r med med ?(a, b).R
       quad attach(gt.tri, br: 1 pi) quad
       (nu b z)((nu a v)(R | P) | Q)
    $],
    [(R-$times.o amp.inv$)],

    [$ lt.tri "inr"(z.P) med med arrow.l.r med med {v.Q, w.R}
       quad &attach(gt.tri, br: 1 pi) quad
       (nu z v)(P | Q)
    $],
    [(R-$times.o amp_1$)],

    [$ lt.tri "inr"(z.P) med med arrow.l.r med med {v.Q, w.R}
       quad &attach(gt.tri, br: 1 pi) quad
       (nu z w)(P | R)
    $],
    [(R-$times.o amp_2$)],

    [$ ![] med med arrow.l.r med med ?().P
       quad &attach(gt.tri, br: 1 pi) quad
       P
    $],
    [(R-$1 bot$)],
    [], [],
    [$ (nu x y)(x arrow.l.r M | P)
       quad &attach(gt.tri, br: 1 pi) quad
       P{y := M}
    $],
    [(R-AxCut)],
    [$ P; med x M
       quad &attach(gt.tri, br: 1 pi) quad
       P{x := M}
    $],
    [(R-Seq)]
  )
]

== Contraction (Congruences)
#align(horizon)[
#grid(
  columns: (1fr, auto), // Left column takes all space, right column fits the name
  row-gutter: 2em,
  align: (center, right + horizon),
  [#prooftree(
    rule(
      name: "",
      $(nu x y)(P | Q) med &attach(gt.tri, br: 1 pi) med (nu x y)(P' | Q)$,
      $P med &attach(gt.tri, br: 1 pi) med P'$
    )
  )],
  [(R-CongCut)],

  [#prooftree(
    rule(
      name: "",
      $P; med x M med &attach(gt.tri, br: 1 pi) med P'; med x M$,
      $P med &attach(gt.tri, br: 1 pi) med P'$
    )
  )],
  [(R-CongSeq)],

  [#prooftree(
    rule(
      name: "",
      $P med &attach(gt.tri, br: 1 pi) med Q$,
      $P equiv P'$,
      $P' med &attach(gt.tri, br: 1 pi) med Q'$,
      $Q' equiv Q$
    )
  )],
  [(R-Struct)]
)
]

== Redexes and Structural Congruence
\
#remark[
  $equiv$ does *not* preserve the set of redexes that are *syntactically* contained within a process. Consider
  #v(1em)
  $
    (nu x y)(a arrow.l.r M_1 | (nu v w) (y arrow.l.r M_2 | P))
  $
  #v(1em)
  which does not contain a redex (syntactically). But
  #v(1em)
  $
    & quad
    (nu x y)(a arrow.l.r M_1 | (nu v w) (y arrow.l.r M_2 | P)) \
    equiv & quad
    (nu v w) ((nu x y) (a arrow.l.r M_1 | y arrow.l.r M_2) | P) \
    equiv & quad
    (nu v w) ((nu y x) (y arrow.l.r M_2 | a arrow.l.r M_1) | P) \
    attach(gt.tri, br: 1 pi) & quad
    (nu v w)((a arrow.l.r M_2){x := M_2} | P)
  $
  #v(1em)
]

= A Note on Asynchronicity
==
#box(
  width: 100%,
  height: 20cm, // Adjust height to cut off right after the authors/abstract
  clip: true,
  stroke: 0.0pt + black,
  image("paper/deyoung-asyn-cut-reduction.pdf", page: 1, width: 100%)
)

== Asychronous Input/Output
#align(horizon)[
$
  #prooftree(
    rule(
      name: $times.o R$,
      $Delta_1, Delta_2 tack.r (nu y) (nu x') (overline(x)chevron.l y,x' chevron.r | P_1 | P_2) :: x : A times.o B$,
      $Delta_1 tack.r P_1 :: y:A$,
      $Delta_2 tack.r P_2 :: x':B$
    )
  )
  \ \ \ \
  #prooftree(
    rule(
      name: $times.o L$,
      $Delta', x : A times.o B tack.r x(y, x').Q :: z : C$,
      $Delta', y : A, x' : B tack.r Q :: z : C$
    )
  )
  \ \ \ \
  (nu x)((nu y)(nu x')(overline(x) chevron.l y, x' chevron.r | P_1 | P_2) | x(y, x').Q) arrow.long.r (nu x')(P_2 | (nu y)(P_1 | Q))
$
]

#pagebreak()
The intermediate syntax $overline(x) chevron.l y, x' chevron.r$ can be mapped into a $pi$FD process:
#v(1em)
$
  overline(x) chevron.l y, x' chevron.r tilde.eq
  x arrow.l.r v; med v![y'.y arrow.l.r y' | x.x arrow.l.r x']
$
#v(1em)
We can thus define
#v(1em)
$
  (nu y)(nu x')(overline(x) chevron.l y, x' chevron.r | P_1 | P_2)
  tilde.eq
  (nu x' x')((nu y y)(x arrow.l.r v; med v![tilde(y).y arrow.l.r tilde(y) | tilde(x).x arrow.l.r tilde(x)] | P_1) | P_2) =: R
$
#v(1em)
In particular, the reduction rule above is derivable:
#v(1em)
$
  & quad(nu x)((nu y)(nu x')(overline(x) chevron.l y, x' chevron.r | P_1 | P_2) | x(y, x').Q) \
  tilde.eq & quad
  (nu x x)(R | x med arrow.l.r med ?(y, x').Q) \
  attach(gt.tri, br:1 pi, tr: *) & quad
  (nu x' x') ((nu y y) (Q | P_1) | P_2)
  tilde.eq  (nu x')(P_2 | (nu y)(P_1 | Q))
$

= Some Metatheory
== Type Safety
#align(horizon)[
// #remark[
//   The formalization uses parallel substitutions opposed to single substitutions presented above.
// ]

#theorem(title: "Preservation", mechanized: true)[
  If $Gamma tack.r Q$ and $P attach(gt.tri, br: 1 pi) Q$, then $Gamma tack.r Q$.
]
#theorem(title: "Progress", mechanized: true)[
  If $Gamma tack.r P$, then there exists $Q$ such that $P attach(gt.tri, br: 1 pi) Q$ or $P$ is final.
]
]
#corollary(title: "Progress for closed processes", mechanized: true)[
  If $tack.r P$, then $P = "stop"$ or there exists $Q$ such that $P attach(gt.tri, br: 1 pi) Q$.
]

== Substitution
#align(horizon)[
#remark[
  The formalization uses parallel substitutions similar to Autosubst (#cite(label("schäfer:2015:autosubst"), form: "prose"))
]

#definition(title: "Typing for substitutions")[
  $
    epsilon tack.r epsilon : epsilon
    quad quad
    #prooftree(
      rule(
        name: $$,
        $x : tau, Gamma tack.r M dot sigma : Delta$,
        $x : tau, Gamma "WF"$,
        $Delta_M tack.r M : tau$,
        $Gamma tack.r sigma : Delta'$,
        $Delta = Delta_M compose Delta'$
      )
    )
  $
]
#lemma(title: "Substitution preserves typing", mechanized: true)[
  #enum(numbering: "(i)")[
    If $Gamma tack.r P$ and $Gamma tack.r sigma : Delta$, then $Delta tack.r P[sigma]$.
  ][
    If $Gamma tack.r M$ and $Gamma tack.r sigma : Delta$, then $Delta tack.r M[sigma]$.
  ][
    If $Gamma tack.r S$ and $Gamma tack.r sigma : Delta$, then $Delta tack.r S[sigma]$.
  ]
]
]

= Final Processes
== Final Processes and Irreducibility
#align(horizon)[
#definition(title: "Final process")[
  A process $P$ is final if one of the following holds
  #set enum(numbering: "(i)")
  + $P = "stop"$
  + $P equiv x arrow.l.r M$
  + $P equiv (nu x_1 y_1)( cal(L)_1 | (nu x_2 y_2)( cal(L)_2 | dots.h.c med (nu x_n y_n)( cal(L)_n | attach(cal(L), br: n + 1) ) med dots.h.c ) )$ such that forall $i$,
    $cal(L_i) equiv a_i arrow.l.r M_i$ ($M_i eq.not y med forall y$) and $a_i$ free
    or $cal(L)_i equiv a_i arrow.l.r b_i$ and $a_i$, $b_i$ free.
]

#lemma(title: "Final and irreducible processes coincide")[
  If $Gamma tack.r P$, then $P$ is final iff $P$ is irreducible.
]
]

= Church-Rosser
==
\
#align(center)[
#cetz.canvas({
  import cetz.draw: *

  content(((0,0), 0, (0,0)), box(fill: white, $ (nu x y)( ![] arrow.l.r ?().P | y arrow.l.r M) $))
  content(((5,-2.5), 0, (0,0)), box(fill: white, $ (nu x y)(P | y arrow.l.r M) $))
  content(((-5,-2.5), 0, (0,0)), box(fill: white, $ ![] arrow.l.r ?().P{x := M} $))
  content(((0,-5), 0, (0,0)), box(fill: white, $ P{x := M} $))

  line((0.5,-0.5), (5, -2), name: "l1")
  line((-0.5,-0.5), (-5, -2), name: "l2")
  line((-5, -3), (-0.5, -4.5), name: "l3")
  line((5, -3), (0.5, -4.5), name: "l4")

  content(("l1.start", 50%, "l1.end"), box(fill: white, inset: 4pt, [$attach(gt.tri, br: 1 pi)$]))
  content(("l2.start", 50%, "l2.end"), box(fill: white, inset: 4pt, [$attach(gt.tri, br: 1 pi)$]))
  content(("l3.start", 50%, "l3.end"), box(fill: white, inset: 4pt, [$attach(gt.tri, br: 1 pi)$]))
  content(("l4.start", 50%, "l4.end"), box(fill: white, inset: 4pt, [$attach(gt.tri, br: 1 pi)$]))
})
]

== Church-Rosser
\ \
#definition(title: $"Reduction" gt.tri$)[
  Reduction $gt.tri$ is defined as the transitive closure of the union of contraction and structural congruence:
  $
    gt.tri med := med attach((attach(gt.tri, br: 1 pi) union equiv), tr: *)
  $
]

#conjecture(title: "Church-Rosser")[
  If $P gt.tri Q_1$ and $P gt.tri Q_2$, then there exists $R$ such that
  $Q_1 gt.tri R$ and $Q_2 gt.tri R$.
]

== References
#bibliography("bibliography/bibliography.bib")