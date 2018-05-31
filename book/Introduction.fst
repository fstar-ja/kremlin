(* {{{ This fslit's file prelude. TODO: find a way to hide this. *)
module Introduction

// Generate a dependency on LowStar.fst which does not have a main but which
// we still want to verify
let _ = LowStar.test_get
(* }}} *)

/// .. fixme-authors::
///     JP Jonathan Protzenko
///
/// 導入
/// ====
///
/// このドキュメントは F* のサブセットである Low* を解説します。
/// この Low* は KreMLin コンパイラを通じてC言語にコンパイルされます。
/// 名前が表わす通り Kre\ **ML**\ は F* プログラムをエクストラクトして実行するための
/// OCa\ **ML** の代替です。
///
/// Low* は単なる言語のサブセットであるだけでなく、C言語の *整理された*
/// 機能をモデル化する F* ライブラリの集合です:
/// それらはC言語のメモリモデル、スタック/ヒープに確保された配列、機種依存整数、
/// C言語文字列リテラル、そして標準Cライブラリに対するいくつかのシステムレベル関数です。
///
/// Low* を書くことで、プログラマは F* の証明と仕様記述の力を最大限享受できます。
/// コンパイル時に証明は削除され、C言語へコンパイルされる低レベルコードだけが残ります。
/// 要するに:
///
/// .. centered:: **コードは低レベルだけれど、検証はそうではありません**。
///
/// このマニュアルは Low* の概要とそのライブラリについて説明し;
/// KreMLin ツールとC言語プログラムやライブラリを生成する様々な方法を示し;
/// いくつかの高度な例を示します。
///
/// Low* は `HACL* <https://github.com/mitls/hacl-star>`_ を作成することに成功しています。
/// このライブラリは Firefox、Linux カーネルやその他のプロジェクトから使用される検証された暗号プリミティブです。
///
/// このチュートリアルは読者が F* を熟知していることを仮定しています;
/// もし疑問があれば、F* の `チュートリアル <https://fstar-lang.org/tutorial>`_
/// を読んでください。
/// (訳注: 左記チュートリアルには日本語訳 http://fstar-ja.metasepi.org/doc/tutorial/ もあります。)
///
/// Low* のエッセンス
/// ----------------
///
/// 次のコードは古典的な ``memcpy`` 関数を実装しています。
/// 型 ``a`` の ``len`` 要素を ``src`` から ``dst`` へコピーします。

#set-options "--use_two_phase_tc true"

open FStar.HyperStack.ST

module S = FStar.Seq
module B = FStar.Buffer
module M = FStar.Modifies
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

let slice_plus_one #a (s1 s2: S.seq a) (i: nat): Lemma
  (requires (
    i < S.length s1 /\
    i < S.length s2 /\
    S.equal (S.slice s1 0 i) (S.slice s2 0 i) /\
    S.index s1 i == S.index s2 i))
  (ensures (
    S.equal (S.slice s1 0 (i + 1)) (S.slice s2 0 (i + 1))))
  [ SMTPat (S.slice s1 0 (i + 1)); SMTPat (S.slice s2 0 (i + 1)) ]
=
  let x = S.index s1 i in
  let s1' = S.append (S.slice s1 0 i) (S.cons x S.createEmpty) in
  let s2' = S.append (S.slice s2 0 i) (S.cons x S.createEmpty) in
  assert (S.equal s1' (S.slice s1 0 (i + 1)));
  assert (S.equal s2' (S.slice s2 0 (i + 1)))

#set-options "--max_fuel 0 --max_ifuel 0"
val memcpy: #a:eqtype -> src:B.buffer a -> dst:B.buffer a -> len:U32.t -> Stack unit
  (requires fun h0 ->
    let l_src = M.loc_buffer src in
    let l_dst = M.loc_buffer dst in
    B.live h0 src /\ B.live h0 dst /\
    B.length src = U32.v len /\
    B.length dst = U32.v len /\
    M.loc_disjoint l_src l_dst)
  (ensures fun h0 () h1 ->
    let l_src = M.loc_buffer src in
    let l_dst = M.loc_buffer dst in
    B.live h1 src /\
    B.live h1 dst /\
    M.(modifies l_dst h0 h1) /\
    S.equal (B.as_seq h1 dst) (B.as_seq h0 src))
let memcpy #a src dst len =
  let h0 = ST.get () in
  let inv h (i: nat) =
    B.live h src /\ B.live h dst /\
    M.(modifies (loc_buffer dst) h0 h) /\
    i <= U32.v len /\
    S.equal (Seq.slice (B.as_seq h src) 0 i) (Seq.slice (B.as_seq h dst) 0 i)
  in
  let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v len }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 () h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
  =
    let open B in
    dst.(i) <- src.(i)
  in
  C.Loops.for 0ul len inv body

let main (): Stack C.exit_code
  (requires fun _ -> True)
  (ensures fun h _ h' -> M.modifies M.loc_none h h')
=
  push_frame ();
  let src = B.createL [ 1UL; 2UL ] in
  let dst = B.create 0UL 2ul in
  memcpy src dst 2ul;
  pop_frame ();
  C.EXIT_SUCCESS

/// この例は Low* のいくつかの機能を含んでいます。
/// まずはじめに高いレベルからのポイントを示します。
/// それからC言語コードにコンパイルする方法を説明します。
/// Low* の詳細な議論はこのチュートリアルの残りの章で説明します。
///
/// このコードは "標準Low*ライブラリ" の一部であるいくつかのモジュールを開きます。
///
/// - ``Buffer`` はスタック/ヒープに確保されたC言語配列のモデルです
///   (:ref:`buffer-library` で解説します)
/// - ``Seq`` は標準F*ライブラリにおけるシーケンス抽象で、
///   これは証明レベルでヒープ中のバッファの中身を扱うために ``Buffer`` を使います
/// - ``Modifies`` はバッファ、参照そしてリージョン上に全称化された modifies 節を提供します (:ref:`modifies-library` で解説します)
/// - ``UInt32`` は C11 ``uint32_t`` 型のモデルで、証明レベルでは自然数と考えます (:ref:`machine-integers` で解説します)
/// - ``HyperStack`` はC言語メモリレイアウトのモデルです (:ref:`memory-model` で解説します)
/// - ``C`` and ``C.Loops`` いくつかのC言語の概念を F* に公開します (:ref:`c-library` で解説します)
///
/// 最初の定義はシーケンスに対する補題です:
/// もし2つのシーケンスがスライス ``[0; i)`` 上で等しくかつ、それら ``i`` 番目の要素が等しいなら、それらのシーケンスはスライス ``[0; i + 1)`` 上で等しくなります。
/// この補題は ``memcpy`` の関数的な正しさを証明するために必要です。
/// 補題は消去され、生成されたコードには現われません。
/// そのため Low* コードに補題を安全に混ぜることができます。
///
/// 次に、``memcpy`` 関数が定義され、活性と互いに素な述語を使った事前/事後条件で注釈されています。
/// 事後条件は ``memcpy src dst len`` が呼び出された後において、
/// コピー先とコピー元がインデックス ``len`` まで同じ内容物を持つことを表明しています。
///
/// ``memcpy`` の実装はC言語スタイルのループ不変条件とループ本体をともなった ``for`` ループを使っています。
/// あるいは、C言語コンパイラが末尾再帰最適化をしてくれることを願って、再帰関数を書くこともできます。
///
/// 最後に、``main`` 関数は ``push_frame`` と ``pop_frame`` を使います。
/// メモリモデルにおけるこの2つのコンビネータは概念上、このコードが新しいスタックフレームで実行されることを示しています。
/// この新しいスタックフレームにおいて、2つのテスト用配列がスタックに確保されます。
/// 機種依存整数を表わす Low* の接尾辞 ``UL`` で示される通り、64ビット符号なし整数の配列になります。
/// ``memcpy`` 関数はこれら2つの配列をともなって呼び出されます。
/// 検証の観点からは、``main`` が呼び出された後にこのスタックフレームは解放されるので、
/// ``main`` がバッファを変更しないことを示せます。
///
/// これらの概念の詳細な説明は後の章で説明するとして、現時点ではこれで十分です。
/// 上記のコードをC言語に変換するために、KreMLin コンパイラを起動できます:
///
/// .. code-block:: bash
///
///    $ krml -no-prefix Introduction introduction.fst
///
/// .. warning::
///
///    このチュートリアルは
///    `fslit <https://github.com/FStarLang/fstar-mode.el/tree/master/etc/fslit>`_
///    を使って書かれています。
///    これはこのドキュメントがHTMLに変換できる F* ソースファイルであることを意味しています。
///    このファイルは ``Introduction.fst`` で、KreMLin の ``book`` ディクトリに見つかるはずです。
///    そのため、もしやってみたければ、自分で実際に実行することができます!
///
/// これでカレントディレクトリにいくつかのC言語ファイルが生成されます。
/// 出力された ``Introduction.c`` は次のようになるでしょう。
///
/// .. code-block:: c
///
///    /* This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
///     * KreMLin invocation: krml -no-prefix Introduction introduction.fst
///     * F* version: 451c4a69
///     * KreMLin version: 3d1941d0
///     */
///
///    #include "Introduction.h"
///
///    void memcpy__uint64_t(uint64_t *src, uint64_t *dst, uint32_t len)
///    {
///      for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
///        dst[i] = src[i];
///    }
///
///    exit_code main()
///    {
///      uint64_t src[2U] = { (uint64_t)1U, (uint64_t)2U };
///      uint64_t dst[2U] = { 0U };
///      memcpy__uint64_t(src, dst, (uint32_t)2U);
///      return EXIT_SUCCESS;
///    }
///
/// 上記は Low* の鍵となるデザインのいくつかを協調しています。
///
/// - **C言語の shallow embedding**。プログラマはC言語へコンパイルされることを念頭にして、F* の構文を書きます。
///   すなわちその構文は Low* サブセットです。
///   私達は生成されたC言語にきめ細かい制御を可能にする ``C.Loops.for`` 関数のようなプリミティブを提供しています。
///
/// - **C言語のモデル**。上記の例は、境界のある機種依存得整数、
///   スタックに確保された配列、スタックとヒープの分離といったような
///   F* におけるいくつかのC言語の機能モデルに依存しています。
///   ``push_frame`` や ``pop_frame`` のような特化したコンビネータは
///   F* 組み込みの作用を使ってコールスタックの構造を考慮することができます。
///
/// - **低レベルなコードに対する高レベルな検証**。 この例は一時的な安全性(活性)
///   から(互いに素でインデックスが範囲外であるような)空間的な安全性に及ぶ
///   膨大な量の仕様を含んでいます。
///   バッファや機種依存整数のような命令的なデータ構造は、
///   証明レベルではそれぞれシーケンスと自然数に反映されます。
///   これは ``memcpy`` を呼び出した後に ``src`` と ``dst`` バッファが ``len``
///   だけ同じであることを表明するような、強力な仕様スタイルを可能にします。
///   この仕様の全ては消去され、簡潔な低レベルな ``for`` ループだけが残されます。
///
/// - **プログラマの生産性のためのツールサポート**。 この例は KreMLin
///   が上記の多相的な ``memcpy`` 関数を単相的なインスタンスを自動生成することに頼っています。
///   高レベルなコンパイラの機能があったても、KreMLin
///   はプログラミング体験の向上に貢献します。
///   Low* ではデータ型、パターンマッチ、タプルを利用できます。
///   それらはそれぞれC言語のタグ付き共用体、``if``
///   の重なり、値によって渡される構造体にコンパイルされます。
///
/// ツールとセットアップ
/// -------------------
///
/// ツールの使い方を紹介し、動作する F*/KreMLin ペアを入手しましょう。
///
/// KreMLin は F* と親密に連携しています:
///
/// - KreMLin の ``master`` ブランチは F* の ``stable`` ブランチと連携しています
/// - KreMLin の ``fstar-master`` ブランチは F* の ``master`` ブランチと連携しています。
///
/// F* の急速な開発のために、このチュートリアルでは *後者* のリビジョンに追従します。
/// これはこのチュートリアルが次のような読者を想定していることを意味しています:
///
/// - F* ``master`` ブランチの最新版を `ソースからビルド
///   <https://github.com/FStarLang/FStar/blob/master/INSTALL.md>`__ していて
/// - KreMLin ``fstar-master`` ブランチの最新版を `ソースからビルド
///   <https://github.com/FStarLang/kremlin/tree/fstar-master/#trying-out-kremlin>`__ していて
/// - パスにC言語コンパイラ、できれば最新のGCC、があること。
///
/// .. note::
///
///    Windows では F* を同様に設定していることを想定します。
///    すなわち `Windows OCaml
///    <https://github.com/fdopen/opam-repository-mingw/>`_
///    をともなった Cygwin 環境に MinGW 64-bit コンパイラが
///    cygwin パッケージ ``x86_64-w64-mingw32-gcc``
///    としてインストールされている必要があります。
///
/// KreMLin ツールの使い方
/// ---------------------
///
/// KreMLin コンパイラはコマンドラインツールの ``krml`` です。
/// ``krml -help`` はオプションを警告のリストを表示することを覚えておいてください。
///
/// F* からC言語へのエクストラクトのプロセスは次のようになります:
///
/// 1. ``fstar.exe`` を呼び出して ``.krml`` ファイル群を生成し、
/// 2. 上記のファイル群に ``krml`` を呼び出してC言語ファイル群を生成し、
/// 3. C言語コンパイラを呼び出して実行ファイルを生成します。
///
/// KreMLin は上記の最初と最後のを自動化でき、F*
/// とC言語コンパイラ両方のドライバとしての機能を果たします。
/// これによって編集/コンパイルを迅速に行なえます。
/// 先のファイルについて、次のように使えます:
///
/// .. code-block:: bash
///
///    $ krml introduction.fst -no-prefix Introduction -o test.exe && ./test.exe
///
/// このチュートリアルではもっぱら上記のコマンドを使います。
/// 上記は簡単に使えて、``Makefile`` を書かずに KreMLin を試用できるためです。
/// さらにビルドの正しいステップでインクルードされるように
/// ``.c``、``.h``、``.o`` そして ``.S`` ファイルを KreMLin に渡すことができます。
/// C言語リンカとコンパイラオプションを KreMLin の ``-ccopt`` と ``-ldopt``
/// オプションを通じて渡せます。
///
/// .. fixme:: JP
///
///    Add a forward pointer to section 8.
///
/// けれども、KreMLin をドライバとして使うのは以下2つの点で効果的ではありません:
///
/// - ステップ1では F* の "旧式" のエクストラクトを使います:
///   ファイル群はシーケンシャルに処理され、キャッシュされません。
///   さらにデフォルトでは検証は実行されません (``-verify`` を使う必要がります)
/// - ステップ3が並列実行ではありません
///
/// ??章では、 検証とエクストラクトを並列で実行し、結果得られたC言語コードを並列にコンパイルする
/// Makefile の具体的な例を提供します。
/// 上記は F* の自動化された依存性解析と ``gcc -MM``
/// を利用していて、インクリメンタルなビルドができます。
