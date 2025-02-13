#import "template.typ": *

#show: project.with(
  title: "Kripke不完全な様相論理",
  authors: ("SnO2WMaN",),
  meta: json("meta.json"),
)

#let AxiomH = $Axiom(H)$
#let LogicKH = $Logic("KH")$


= 本文

標準的な様相論理において，Kripke意味論は有用ではあるが，万能ではない．
例えば，非反射的なKripkeフレームのクラスを標準的な様相論理で特徴づけることは出来ないことはよく知られている．
更に微妙な結果として，Kripke意味論に対して完全ではない，すなわちKripke不完全な様相論理も存在する．
この文書では $LogicKH$ がKripke不完全であることの証明を載せておく．
証明は @hughesNewIntroductionModal2007 および @boolosLogicProvability1994 に基づく#footnote[ただし @boolosLogicProvability1994 に記載されている証明は大枠では正しいが，細部が誤っている気がする．誤植だろうか？]．

#notation[
  この文書では以下の用に用語を用いる．

  - 論理とはHilbert流の証明体系を表すものとする．
  - 単にフレームと言ったら Kripkeフレームのことを指すものとする．同様に，モデルと言ったら Kripkeモデルのことを指すものとする．
]

#definition[様相論理の公理][
  命題変数 $p$ を一つ固定して，以下の公理を定める．
  $
    Axiom4 &equiv box p -> box box p \
    AxiomL &equiv box(box p -> p) -> box p \
    AxiomH &equiv box(box p <-> p) -> box p
  $

  $p$ を適当な論理式で置き換えることで得られる論理式を，公理のインスタンスという．
]

#definition[
  公理を追加するとは，全ての公理のインスタンスを証明可能な論理式として追加することを指す．

  - $LogicK$ に公理 $AxiomL$ を追加した論理は $LogicGL$ と呼ばれる．
  - $LogicK$ に公理 $AxiomH$ を追加した論理は $LogicKH$ と呼ばれる．
]

#remark[歴史的経緯，@KurahashiShomeikanoseironri2016[pp.109-111]][
  $LogicGL$ は不完全性定理における証明可能性述語の挙動を様相論理によって分析する証明可能性論理と呼ばれる分野でよく知られている．
  不完全性定理は「自分自身の正しさと*反証可能性*が同値である文#footnote[このような文を構成する補題がいわゆる対角化補題である．]の挙動はどうなるか？」という問に対する系であるとも考えられる．
  これを踏まえて，Henkinは「では，自分自身の正しさと自分自身の*証明可能性*が同値である文の挙動はどうなるか？」という問題を提起した．
  次のLöbの定理はこの問に対する回答であり，特に同値性は必要なく，片側の含意だけで良いことがわかった．
  #theorem(numbering: none)[Löbの定理][
    $T vdash Pr(T)(GoedelNum(sigma)) -> sigma$ ならば $T vdash sigma$．
  ]
  更にこれを形式化することで次の定理も得られる．
  #theorem(numbering: none)[形式化されたLöbの定理][
    $T vdash Pr(T)(GoedelNum(Pr(T)(GoedelNum(sigma)) -> sigma)) -> Pr(T)(GoedelNum(sigma))$．
  ]
  公理 $AxiomL$ は形式化されたLöbの定理に対応している．
  では，元々のHenkinの問題で要請されていた同値性に関しては結局どうなるのだろうか？
  これに対応する公理が $AxiomH$ である．
]

$LogicKH$ はKripke意味論に対して完全ではない論理の一つである．
すなわち，@thm:KH_incompleteness が成り立つ．

#theorem[$LogicKH$のKripke不完全性][
  $LogicKH$ に対して健全かつ完全なフレームのクラスは存在しない．
  すなわち，任意の論理式 $phi$ に対して，以下を満たすフレームクラス $C$ は存在しない．
  $
    LogicKH vdash phi <==> forall F in C. F vDash phi
  $
] <thm:KH_incompleteness>

@thm:KH_incompleteness は @thm:Four_of_F と @thm:KH_not_prove_Axiom4 から従う．

#lemma[
  任意のフレーム $F$ に対し，次が成立する．
  $
    F vDash AxiomH ==> F vDash Axiom4
  $
] <thm:Four_of_F>

#lemma[
  $LogicKH nvdash Axiom4$．
] <thm:KH_not_prove_Axiom4>


#proof[@thm:KH_incompleteness][
  仮にそのようなクラスが $C$ として存在したとする．
  $LogicKH$ では明らかに公理 $AxiomH$ が証明可能なので，$C vDash AxiomH$ が成立する．
  @thm:Four_of_F より $C vDash Axiom4$ が成立する．
  よって $LogicKH vdash Axiom4$．
  しかし @thm:KH_not_prove_Axiom4 よりこれはおかしい．
]

それでは @thm:Four_of_F と @thm:KH_not_prove_Axiom4 を示そう．

== @thm:Four_of_F の証明

こちらの証明は比較的簡単である．
まず，次の事実が成り立つ．証明は省略する．

#proposition[
  フレーム $F$ に対し，$F vDash AxiomL$ なら，$F$ は推移的であり，したがって $F vDash Axiom4$ である．
] <prop:validate_4_of_validate_L>

次に，$AxiomH$ と $AxiomL$ はKripkeフレーム上では区別がつかないことを示す．

#lemma[
  任意のフレーム $F$ に対し，次が成立する．
  $
    F vDash AxiomH <==> F vDash AxiomL
  $
] <lem:validate_H_iff_validate_L>

#proof[
  #struct[
    $==>$ を示す．
  ]
  #struct[
    $<==$ を示す．
  ]
]

後は簡単である．

#proof[@thm:Four_of_F][
  @prop:validate_4_of_validate_L と @lem:validate_H_iff_validate_L より明らか．
]

== @thm:KH_not_prove_Axiom4 の証明

こちらはややテクニカルな議論が必要である．
@thm:KH_not_prove_Axiom4 を示す前に次の補題を用意しておこう．

#lemma[
  $LogicK$ に公理 $Sigma$ を追加した論理体系を $Logic(K Sigma)$ とする．
  あるモデル $M$ が $Sigma$ の*公理のインスタンス*を全て妥当にするなら，$Logic(K Sigma) vdash phi ==> M vDash phi$．
] <lem:model_existence>

#proof[
  命題論理のトートロジー，公理 $AxiomK$ のインスタンスは任意のモデルで妥当であり，
  また推論規則モーダス・ポネンス，ネセシテーションはモデルによる妥当性を保存する．
  これらの事実と $Sigma$ の公理のインスタンスが全て妥当であるという仮定を用いて，
  $Logic(K Sigma) vdash phi$ のHilbert流証明体系での証明による帰納法を回せば良い．
]

@thm:KH_not_prove_Axiom4 は @lem:model_existence の対偶を用いて証明する．

#proof[@thm:KH_not_prove_Axiom4][
  @lem:model_existence の対偶より，$AxiomH$ のインスタンスを全て妥当にし，$Axiom4$ を妥当にしないモデルが存在することを示せば十分であり，
  Cresswellのモデルと呼ばれるモデルはその条件を満たす．
]

それでは実際に Cresswellのモデルを定義し，実際に条件を満たすか確認する．

#let CresswellModel = $M_upright("C")$

#definition[Cresswellモデル][
  Cresswellのモデル $CresswellModel := angle.l W, R, forces angle.r$ は以下のように定義される．

  まず $NN$ を自然数全体の集合として，$NN^sharp, NN^flat$ の2つの集合を定める．$NN^sharp sect NN^flat = emptyset$ である．
  $
    NN^sharp = { 0^sharp, 1^sharp, 2^sharp, ...} \
    NN^flat = { 0^flat, 1^flat, 2^flat, ...}
  $

  $W = NN^sharp union NN^flat$ とする．

  次に $R$ を以下のように定める．任意の $n,m in NN$ に対して

  1. $n^sharp R m^sharp &<==> n <= m + 1$
  2. $n^flat R m^flat &<==> n > m$
  3. $n^sharp R m^flat$

  最後に，$w forces a <==> w != 0^sharp$ と定める．
]

#remark[
  フレームを図示すると以下のようになる．
  $
    0^sharp, 1^sharp, 2^sharp, ..., n^sharp, ..., m^flat, ..., 2^flat, 1^flat, 0^flat
  $
]

まず公理 $Axiom4$ がCresswellのモデルでは妥当でないことを示そう．

#lemma[$CresswellModel, 2^sharp nvDash Axiom4$．] <lem:Cresswell_not_validate_Axiom4>

#proof[

]

次に，$AxiomH$ の全てのインスタンスがCresswellのモデルで妥当であることを示す．
その前にTruthsetと呼ばれる集合とその補題を準備する．

#definition[
  $phi$ に対して ${ x | CresswellModel, x vDash phi }$ を $[phi]$ と書いて，$phi$ のTruthsetと呼ぶ．
]

#lemma[
  任意の $phi$ に対し，$[phi]$ またはその補集合 $[phi]^c$ のどちらかは有限である．
] <lem:truthset_either_finite>

では示そう．

#lemma[
  $AxiomH$ の全てのインスタンスは $M$ で妥当．
] <lem:Cresswell_validate_AxiomH>



== その他

$LogicKH$ については他に以下のような性質が知られている．

#proposition[
  $LogicGL$ は $LogicKH$ より真に強い．
  すなわち，$LogicKH$ で証明できる論理式は $LogicGL$ でも証明できるが，$LogicGL$ で証明可能であっても $LogicKH$ で証明できない論理式が存在する．
]
#proof[
  適当に計算すると，$LogicGL$ は公理 $AxiomH$ および $Axiom4$ を証明することが出来ることがわかる．
  一方，@thm:KH_not_prove_Axiom4 より $Axiom4$ は $LogicKH$ では証明できない．
]

Kripke不完全性を起こしている原因の一つは $LogicKH$ では $Axiom4$ が証明できないことにあった．
では $Axiom4$ を追加するとどうなるか？これは以下が知られている．

#proposition[@KurahashiShomeikanoseironri2016[p.113]][
  $LogicKH$ に $Axiom4$ を足した論理は $LogicGL$ になる．
]
