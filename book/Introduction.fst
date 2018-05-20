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
/// (訳注: 上記チュートリアルには日本語訳 http://fstar-ja.metasepi.org/doc/tutorial/ もあります。)
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
/// - **High-level verification of low-level code**. The example contains a vast
///   amount of specification, ranging from temporal safety (liveness) to
///   spatial safety (disjointness, indices within bounds). Imperative data
///   structures, such as buffers or machine integers, are reflected at the
///   proof level with sequences and natural numbers respectively. This allows
///   for a powerful specification style, which ultimately states that after
///   calling ``memcpy``, the ``src`` and ``dst`` buffers are the same up to ``len``.
///   All of this specification is erased, leaving only a succinct, low-level
///   ``for``-loop.
///
/// - **Tooling support for programmer productivity**. The example relies on
///   KreMLin to automatically generate monomorphic instance of the polymorphic
///   ``memcpy`` function above. This is representative of a more general take:
///   whenever there is a predictable compilation scheme for a high-level
///   feature, KreMLin will provide support to enhance the programming
///   experience. In Low*, one enjoys data types, pattern-matching, tuples,
///   which are respectively compiled as C tagged unions, cascading
///   ``if``\ s, or structures passed by value.
///
/// Tooling and setup
/// -----------------
///
/// We now show how to get started with the tools and obtain a working F*/KreMLin
/// pair.
///
/// KreMLin is intimately tied with F*:
///
/// - the ``master`` branch of KreMLin works with the ``stable`` branch of F*
/// - the ``fstar-master`` branch of KreMLin works with the ``master`` branch of F*.
///
/// Due to the fast-paced nature of F* development, this tutorial is kept
/// up-to-date with the *latter* set of revisions, meaning that this tutorial
/// expects the user to have:
///
/// - an up-to-date version of F* ``master`` `built from source
///   <https://github.com/FStarLang/FStar/blob/master/INSTALL.md>`__
/// - an up-to-date version of KreMLin ``fstar-master``, `built from source
///   <https://github.com/FStarLang/kremlin/tree/fstar-master/#trying-out-kremlin>`__
/// - a C compiler in the path, preferably a recent version of GCC.
///
/// .. note::
///
///    On Windows, we expect the user to use the same setup as F*, i.e. a Cygwin
///    environment with a `Windows OCaml
///    <https://github.com/fdopen/opam-repository-mingw/>`_, along with the MinGW
///    64-bit compilers installed *as cygwin packages*, i.e. the
///    ``x86_64-w64-mingw32-gcc`` executable, along with the corresponding linker,
///    archiver, etc.
///
/// Usage of the KreMLin tool
/// -------------------------
///
/// The KreMLin compiler comes as a command-line tool ``krml``. As a reminder, ``krml
/// -help`` provides the list of options and warnings along with proper
/// documentation.
///
/// The process of extracting from F* to C involves:
///
/// 1. calling ``fstar.exe`` to generate a set of ``.krml`` files
/// 2. calling ``krml`` on these files to generate a set of C files
/// 3. calling the C compiler to generate an executable.
///
/// KreMLin can automate the first and last steps, and act as a driver for both F*
/// and the C compiler, allowing for a quick edit-compile-cycle. For this present
/// file, one may use:
///
/// .. code-block:: bash
///
///    $ krml introduction.fst -no-prefix Introduction -o test.exe && ./test.exe
///
/// The present tutorial will use this mode exclusively, as it
/// is much easier to use and allows trying out KreMLin without writing a
/// substantial amount of ``Makefile``\ s. Furthermore, one can pass ``.c``, ``.h``,
/// ``.o``, and ``.S`` files to KreMLin, to be included at the right step of the
/// build, along with C linker and compiler options via KreMLin's ``-ccopt`` and
/// ``-ldopt`` options.
///
/// .. fixme:: JP
///
///    Add a forward pointer to section 8.
///
/// However, using KreMLin as a driver is inefficient for two reasons:
///
/// - step 1 uses "legacy" extraction in F*: files are processed sequentially,
///   without caching, and verification is by default not performed (use ``-verify``)
/// - step 3 is not parallel
///
/// Section ?? provides a complete sample Makefile that performs parallel
/// verification and extraction, along with parallel compilation of the resulting C
/// code, using F*'s automated dependency analysis and ``gcc -MM`` for correct,
/// incremental builds.
