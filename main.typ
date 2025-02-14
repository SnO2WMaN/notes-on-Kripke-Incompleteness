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

#remark[
  歴史的経緯を少し触れておく．詳しくは @KurahashiShomeikanoseironri2016[pp.109-111] なども参照のこと．
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
まず，次の事実が成り立つ．

#proposition[
  フレーム $F$ に対し，$F vDash AxiomL$ なら，$F$ は推移的であり，したがって $F vDash Axiom4$ である．
] <prop:validate_4_of_validate_L>
#proof[
  証明略．@sanoModalLogicIntro2016 や @nishimuraModalDefinability2025 などを参照せよ．
]

次の補題が肝心である．

#lemma[
  任意のフレーム $F = angle.l W, R angle.r$ に対し，次が成立する．
  $
    F vDash AxiomH <==> F vDash AxiomL
  $
] <lem:validate_H_iff_validate_L>

#proof[
  $<==$ は素直に計算すればよい．$==>$ を示す．

  $F vDash AxiomH$ と仮定する．
  更に，付値 $forces$ と $x, y in W$ で $x R y$ となるものを任意にとり，$angle.l F, forces angle.r, x vDash box (box p -> p)$ と仮定し，
  $angle.l F, forces angle.r, y vDash p$ を示す．

  次のように付値 $forces'$ を定める．
  $
    w forces' q <==> forall n in NN : angle.l F, forces angle.r, w vDash box^n q
  $

  次が成り立つ．
  $
    angle.l F, forces' angle.r, x vDash box (box p <-> p) #<eq:validate_H_iff_validate_L:1> \
  $
  #struct[
    任意の $x R z$ となる $z$ で
    $angle.l F, forces' angle.r, z vDash p <==> angle.l F, forces' angle.r, z vDash box p$
    となることを示せば良い．

    以下のように示される．
    $
      angle.l F, forces' angle.r, z vDash p
      &<==> forall n in NN : angle.l F, forces angle.r, z vDash box^n p  #<eq:validate_H_iff_validate_L:2> \
      &<==> forall n in NN : angle.l F, forces angle.r, z vDash box^(n + 1) p  #<eq:validate_H_iff_validate_L:3> \
      &<==> forall n in NN : forall w, z R w: angle.l F, forces angle.r, z vDash box^n p \
      &<==> forall w, z R w: angle.l F, forces' angle.r, z vDash p \
      &<==> angle.l F, forces' angle.r, z vDash box p
    $

    @eq:validate_H_iff_validate_L:3 から @eq:validate_H_iff_validate_L:2 を出すことについてだけ注意しておく．
    これは $angle.l F, forces angle.r, z vDash box box^n p -> box^n p$ を示せば良い．
    $n$ についての帰納法を回した時，$n = 0$ のケースは最初の仮定 $angle.l F, forces angle.r, x vDash box (box p -> p)$ より $angle.l F, forces angle.r, z vDash box p -> p$ から従う．$n > 0$ に関しては帰納法の仮定を用いて証明すれば良い．
  ]

  @eq:validate_H_iff_validate_L:1 と $F vDash AxiomH$ を合わせれば次を得る．
  $
    angle.l F, forces' angle.r, x vDash box p #<eq:validate_H_iff_validate_L:4> \
  $

  @eq:validate_H_iff_validate_L:4 と $x R y$ から $angle.l F, forces' angle.r, y vDash p$ が成り立つ．
  $forces'$ の定義より，任意の $n in NN$ に対して $angle.l F, forces angle.r, y vDash box^n p$ が成り立つ．
  特に $n = 0$ とすれば $angle.l F, forces angle.r, y vDash p$ が成り立つ．
]

後は簡単である．

#proof[@thm:Four_of_F][
  @prop:validate_4_of_validate_L と @lem:validate_H_iff_validate_L より明らか．
]

#remark[
  @lem:validate_H_iff_validate_L は，$AxiomL$ によって定義されるフレームのクラスと $AxiomH$ でも定義されるフレームのクラスが一致することを示している．
]

== @thm:KH_not_prove_Axiom4 の証明

こちらはややテクニカルな議論が必要である．
@thm:KH_not_prove_Axiom4 を示す前に次の補題を用意しておこう．

#lemma[
  $LogicK$ に公理の集合 $Sigma$ を全て追加した論理体系を $Logic(K Sigma)$ とする．
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

#definition[Cresswellのモデル][
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
  フレームをわかりやすく図示すると以下のようになる．
  $
    0^sharp, 1^sharp, 2^sharp, ..., n^sharp, ..., m^flat, ..., 2^flat, 1^flat, 0^flat
  $

  $NN^sharp$ では一歩だけ戻ることが出来る，すなわち $(n + 1)^sharp R n^sharp$ である．
  しかし，それ以外では全体的に左から右にしか行けない一方通行であると思えば良い．
]

まず公理 $Axiom4$ がCresswellのモデルでは妥当でないことを示そう．

#lemma[$CresswellModel, 2^sharp nvDash Axiom4$．] <lem:Cresswell_not_validate_Axiom4>

#proof[
  $2^sharp vDash box p$ と $2^sharp nvDash box box p$ を示せば良い．
  $2^sharp$ から1歩だけで行ける世界に $0^sharp$ は存在しない．よって $2^sharp vDash box p$ が成り立つ．
  他方，$2^sharp$ から2歩で行ける世界には $0^sharp$ が存在する．よって $2^sharp nvDash box box p$ が成り立つ．
]

次に，$AxiomH$ の全てのインスタンスがCresswellのモデルで妥当であることを示す．
その前にTruthsetと呼ばれる集合とその補題を準備する．

#definition[
  $phi$ に対して ${ x | CresswellModel, x vDash phi }$ を $[phi]$ と書いて，$phi$ のTruthsetと呼ぶ．
]

#lemma[
  任意の $phi$ に対し，$[phi]$ またはその補集合 $[phi]^c$ のどちらかは有限である．
] <lem:truthset_either_finite>

#proof[
  $phi$ に関する論理式の帰納法で示す．
  #struct[
    $phi equiv p$ なら $[p]^c = {0^sharp}$ なのでよい．
  ]
  #struct[
    $phi equiv bot$ なら $[bot] = emptyset$ なのでよい．
  ]
  #struct[
    $phi equiv psi -> xi$ のとき．
    $[psi -> chi] = [psi]^c union [chi]$ であることに注意する．
    補集合を考えると，$[psi]^c union [chi]$ または $[psi] sect [chi]^c$ のどちらかが有限であることを示せばよい．
    帰納法の仮定を用いれば4パターンに分類出来る．
    #struct[
      $[psi]$ が有限か $[chi]^c$ が有限ならば $[psi] sect [chi]^c$ が有限．
    ]
    #struct[
      $[phi]^c$ が有限かつ $[psi]$ が有限のときは $[psi]^c union [chi]$ が有限．
    ]
    よってよい．
  ]
  #struct[
    $phi equiv box psi$ のとき．

    $NN^flat subset.eq [psi]$ かそうでないかで場合分けを行う．
    #struct[
      そうでないとき，すなわちある $n^flat$ が存在して $n^flat in.not [psi]$ であるとする．

      このとき $[box psi] subset.eq { m^flat | m <= n }$ を示す．
      任意の $x in [box psi]$ が $x in { m^flat | m <= n }$ であることを示せばよい．
      $x$ で場合分けする．
      #struct[
        $x = m^sharp$ であるとき，$m^sharp R n^flat$ だから $n^flat in [psi]$ となっておかしい．
      ]
      #struct[
        $x = m^flat$ であるとき，仮に含まれていない，すなわち $m > n$ と仮定する．
        このとき $m^flat R n^flat$ だから $n^flat in [psi]$ となっておかしい．
      ]

      ${ m^flat | m <= n }$ は有限であるので $[box psi]$ も有限である．
    ]
    #struct[
      $NN^flat subset.eq [psi]$ のとき．
      帰納法の仮定より $[psi]^c$ は有限である．

      $[phi]^c$ が空集合なら $[psi] = W$ であり，$[box psi] = W$ が言える．
      よって $[box psi]^c = emptyset$ であり，これは明らかに有限である．
      したがって，$[psi]^c$ は空集合でないとする．

      最大の $n^sharp in [psi]^c$ を取る．すなわち任意の $n < m$ で $m^sharp in [psi]$ である．

      このとき $[box psi]^c subset.eq { m^sharp | m <= n + 1 }$ であることを示す．
      任意の $x in [box psi]^c$ が $x in { m^sharp | m <= n + 1 }$ であることを示せばよい．
      $x in [box psi]^c$ から更に $x R y$ となる $y$ が存在して $y in.not [psi]$ である．
      $x, y$ で場合分けする．
      #struct[
        $y = k^flat$ ではない．仮に $y = k^flat$ なら，仮定より $k^flat in [psi]$ であり，おかしい．
      ]
      #struct[
        $x = m^flat$ かつ $y = k^sharp$ は $m^flat R k^sharp$ ではないのでありえない．
      ]
      #struct[
        $x = m^sharp$ かつ $y = k^sharp$ であると仮定する．
        $m^sharp R k^sharp$ なので，$m <= k + 1$ である．
        仮に含まれないとすると，$m > n + 1$ である．したがって，$n < k$ であるから，最大値の仮定より $k^sharp in [psi]$ が言えておかしい．
      ]
      ${ m^sharp | m <= n + 1 }$ は有限であるので $[box psi]$ も有限である．
    ]
  ]
  よって示された．
]

では @lem:Cresswell_validate_AxiomH を示そう．

#lemma[
  $AxiomH$ の全てのインスタンスは $M$ で妥当．
] <lem:Cresswell_validate_AxiomH>

#proof[
  論理式 $phi$ による $AxiomH$ のインスタンスを考える．
  任意に $x in W$ とし，$x vDash box(box phi <-> phi) -> box phi$ を示す．

  $NN^flat subset.eq [phi]$ かそうでないかで場合分けを行う．
  #struct[
    そうでないとき，すなわちある $n^flat$ が存在して $n^flat in.not [phi]$ であるとする．

    このとき，一般性を失わずに $n^flat$ は最小，すなわち，任意の $m > n$ に対して $m^flat in [phi]$ としてよい．
    #struct[
      $m^flat in.not [phi]$ かつ，任意の $k > m$ に対して $k^flat in [phi]$ となる $m^flat$ を $0^flat, 1^flat,...$ から探していく．
      例えば，仮に $0^flat in [phi]$ であった場合，次の $1^flat$ について $1^flat in.not [phi]$ であるなら $m^flat = 1^flat$ とすれば良いし，
      そうでないなら次の $2^flat$ について同様に探していく．
      この手続きは $n^flat in.not [phi]$ であることから必ず $n^flat$ までには終わる．
    ]

    この仮定を用いて計算すると，次が成り立つ．
    $
      n^flat &vDash box phi #<eq:Cresswell_validate_AxiomH:case1:1> \
      n^flat &nvDash box phi <-> phi #<eq:Cresswell_validate_AxiomH:case1:2>
    $

    これらを踏まえて，$x$ で場合分けを行う．
    #struct[
      $x = m^sharp$ であるときは $m^sharp R n^flat$ なので @eq:Cresswell_validate_AxiomH:case1:2 より良い．
    ]

    #struct[
      $x = m^flat$ で $m > n$ であるとき，
      $m^flat vDash box (box phi <-> phi)$ と仮定すると $m^flat R n^flat$ であるので
      $n^flat &vDash box phi <-> phi$ となり @eq:Cresswell_validate_AxiomH:case1:1 と矛盾する．
      よって $m^flat nvDash box (box phi <-> phi)$ であり，良い．
    ]

    #struct[
      $x = m^flat$ で $m <= n$ であるとき．
      $m^flat$ から行けるのは $m > k$ として $k^flat$ のみである．
      このとき $n > k$ であるから，$n$ の最小性の仮定より $k^flat in [phi]$ である．
      したがって $m^flat vDash box phi$ が成り立ち，良い．
    ]

    これで任意の $x in W$ に対して $x vDash box(box phi <-> phi) -> box phi$ が成り立つことが示された．
  ]
  #struct[
    $NN^flat subset.eq [phi]$ なら $[phi]$ は無限なので，@lem:truthset_either_finite より $[phi]^c$ は有限である．
    $[phi]^c$ が空集合とすると $x vDash box phi$ が成り立つので良い．
    よって $[phi]^c$ は空集合でないとする．

    最大の $n^sharp in [phi]^c$ を取る．すなわち任意の $n < m$ で $m^sharp in [phi]$ である．

    $x$ について場合分けを行う．
    #struct[
      $x = m^flat$ であるとき，$m^flat$ から行けるのは $NN^flat$ の要素のみであり，$NN^flat subset.eq [phi]$ なので $m^flat vDash box phi$ が成り立つ．
      よってよい．
    ]
    #struct[
      $x = m^sharp$ かつ，$n + 2 <= m$ であるとき．
      このとき $m^sharp$ から行ける世界は全て $NN^flat$ の要素か，$n + 1 <= k$ として $k^sharp$ までである．
      $n$ の最大性の仮定よりこれらの世界は全て $[phi]$ に含まれ，したがって $m^sharp vDash box phi$ が成り立つ．
      よってよい．
    ]
    #struct[
      $x = m^sharp$ かつ，$n + 1 >= m$ であるとき．
      このとき，$m^sharp nvDash box(box phi <-> phi)$ を示す．
      定義より $m^sharp R (n + 1)^sharp$ であるから，$(n + 1)^sharp nvDash box phi <-> phi$ が示されれば十分．
      更に，最大性の仮定より $(n + 1)^sharp vDash phi$ であるから，$(n + 1)^sharp nvDash box phi$ を示せば良い．
      これは定義より $(n + 1)^sharp R n^sharp$ であり，$n^sharp in [phi]^c$ なので成り立つ．
      以上よりよい．
    ]
    これで任意の $x in W$ に対して $x vDash box(box phi <-> phi) -> box phi$ が成り立つことが示された．
  ]
  どちらにしても，$x vDash box(box phi <-> phi) -> box phi$ が成り立つので，
  $CresswellModel vDash box(box phi <-> phi) -> box phi$ が成り立つ．
]

これにより，Cresswellモデルは所望の性質を満たすことが確認できたので，@thm:KH_not_prove_Axiom4 の証明も通る．

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

なお，$LogicGL$ 自体も，非反射的かつ推移的な有限フレームクラスに対して健全かつ完全ではあるが，いかなるフレームクラスに対しても強完全ではないことが知られている．
詳しくは @sanoModalLogicIntro2016[pp.57-66] を参照せよ．
