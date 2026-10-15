import Lean
import Lake

open Lean Elab System
namespace PathModule

/--
パスのコンポーネント (パスの構成要素を分割してリスト化したもの)から相対パスを作る。
-/
def getRelativePartFromComponents (childrenPathComps : List String) (parentPathComps : List String) : Option System.FilePath := do
  match childrenPathComps, parentPathComps with
    -- 子の要素が残ればそこから相対パスが作れる
    | relative, [] => System.mkFilePath relative
    -- 親要素が残っていたらおかしい(親パスだと思っていたものが子パスということなので)
    | [], _ => none
    -- 両リストに要素がまだ残っていたときは先頭要素を比較する
    -- 要素が一致していれば同じパスをたどっていると判断できる
    | (h1 :: r1), (h2 :: r2) =>
      if h1 == h2 then
        -- 再帰的に探索する
        getRelativePartFromComponents r1 r2
      else
        none
/--
子パスと親パスから相対パスを構成する。
-/
def getRelativePart (childrenPath : System.FilePath) (parentPath : System.FilePath) : Option System.FilePath := do
  getRelativePartFromComponents childrenPath.components parentPath.components

/--
パッケージディレクトリまでの相対パスを取得する。
-/
def packageDirectoryPath : System.FilePath :=
  if Lake.defaultPackagesDir == "packages" then
    System.mkFilePath [".lake", Lake.defaultPackagesDir.toString]
  else
    Lake.defaultPackagesDir

/--
ビルドされたファイルが格納されるディレクトリまでの相対パスを取得する。
-/
def buildDirectoryPath : System.FilePath :=
  if Lake.defaultPackagesDir.fileName == "packages" then
    System.mkFilePath [".lake", "build"]
  else
    "build"

/--
パスの構成要素から不要な . を取り除く
-/
private def trimPath (path : FilePath) : FilePath :=
  assert! path.isRelative
  mkFilePath $ path.components.filter (· != ".")

/--
ライブラリディレクトリ (lib) までのパスを取得する。
-/
def libraryDirectoryPath : FilePath :=
  System.mkFilePath [buildDirectoryPath.toString, "lib", "lean"]

/--
絶対パスを構成する。
-/
def getAbsolutePath(path : System.FilePath) : IO System.FilePath := do
  if path.isAbsolute then
    pure path
  else
    let currentDirPath ← IO.currentDir
    pure $ System.mkFilePath [currentDirPath.toString, path.toString]

/--
.leanのファイルパスからそのビルドファイル(.olean)へのパスを取得する。
-/
def fetchBuildFile (subDirectory : FilePath) (path : FilePath) (extension : String) : Option FilePath :=
  let trimmedPath := (trimPath path).withExtension extension
  match getRelativePart trimmedPath $ System.mkFilePath [packageDirectoryPath.toString, "lean4", "src"] with
    | some relativePath =>
      match getRelativePart relativePath (System.mkFilePath ["lean", "lake"]) with
        | some relativePath' =>
          System.mkFilePath [packageDirectoryPath.toString, "lean4", "lib" , "lean", relativePath'.toString]
        | none =>
          System.mkFilePath [packageDirectoryPath.toString, "lean4", "lib", relativePath.toString]
    | none =>
      match getRelativePart trimmedPath packageDirectoryPath with
        | some relativePath =>
          match relativePath.components with
            | [] => none
            | head :: remain => System.mkFilePath [packageDirectoryPath.toString, head, buildDirectoryPath.toString, subDirectory.toString, "lean", (System.mkFilePath remain).toString]
        | none => System.mkFilePath [buildDirectoryPath.toString, subDirectory.toString, "lean", trimmedPath.toString]
/--
oleanのファイルパスからソースとなる lean コードへのパスを取得する。
-/
def fetchSourceFile(oleanFilePath : System.FilePath) : System.FilePath :=
  let pathComponents := (System.mkFilePath $ oleanFilePath.components.filter (· != ".")).withExtension "lean"
  let libDir := (System.mkFilePath ["lean4", "lib"]).toString
  match getRelativePart pathComponents $ packageDirectoryPath / libDir with
  -- .lake/packages/lean4/lib の子ディレクトリにあったとき
  -- `.lake/packages/lean4/lib/lean/Init/Prelude.olean` みたいな場合
  -- この時ソースファイルは `.lake/packages/lean4/src/lean/Init/Prelude.lean` にある
  | some relative =>
    let srcDir := (System.mkFilePath ["lean4", "src"]).toString
    System.mkFilePath [packageDirectoryPath.toString, srcDir ,relative.toString]
  | none =>
    -- パッケージディレクトリ直下にある場合がまだある
    match getRelativePart pathComponents packageDirectoryPath with
      | some relative =>
        -- `.lake/packages/aesop/.lake/build/lib/Aesop.olean` のような場合
        -- `.lake/packages/aesop/Aesop.lean` にソースコードがある
        -- 相対パスの先頭がパッケージ名になっている (上の例だと aesop)
        let packageName := relative.components.head!
        -- oleanファイルのパスから build/libを除きたい
        -- build/libでパスの文字列を除いたうえで olean を除き、ファイル名だけを取得する.
        let separator := (System.mkFilePath ["build", "lib"]).toString
        System.mkFilePath [packageDirectoryPath.toString, packageName, (relative.toString.splitOn separator |>.tail!.head!)]
      | none =>
        getRelativePart pathComponents (System.mkFilePath [buildDirectoryPath.toString, "lib", "lean"]) |> Option.get!

/--
親パスに含まれていて、かつディレクトリが存在しないようなコンポーネントすべてのディレクトリを作成する。
-/
def makeParentDirectories (path : FilePath) : IO Unit := do
  let some parent := path.parent | throw $ IO.userError s!"引数に渡されたパスの親パスを取得できません。 パス : {path}"
  IO.FS.createDirAll parent

/--
モジュール名からLeanファイルのパスを取得する。
-/
def findLeanFile (moduleName : Name) : IO FilePath := do
  Lean.findLean (← Lean.getSrcSearchPath) moduleName
end PathModule
