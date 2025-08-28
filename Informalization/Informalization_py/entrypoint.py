import asyncio
import sys
import ApplicationService.InformalizationService as app
from pathlib import Path
import os
import fnmatch
from typing import List
from tqdm import tqdm
import injector


async def main(path : str):
    pathObj = Path(path)
    if pathObj.suffix == ".lean":
        await execute(pathObj)
        return
    lean_files = find_files(pathObj, 'lean')
    if len(lean_files) == 0:
        raise RuntimeError("Given file path doesn't point to .lean file or lean file directory")
    for lean_file in tqdm(lean_files, "Lean File Progress"):
        await execute(lean_file)

async def execute(path : Path):
    inj = injector.Injector()
    service = inj.get(app.InformalizationService)
    await service.informalize(path)

def find_files(root_dir : Path, extension : str) -> List[Path]:
    """
    再帰的に引数に渡されたディレクトリ以下の特定拡張子のファイルを取得する
    https://cfd.life/column/python%E3%83%87%E3%82%A3%E3%83%AC%E3%82%AF%E3%83%88%E3%83%AA%E5%86%85%E3%81%AE%E7%89%B9%E5%AE%9A%E3%81%AE%E6%8B%A1%E5%BC%B5%E5%AD%90%E3%81%AE%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB%E3%81%AE%E5%90%8D/
    から持ってきたものを一部改変しています
    """
    matches = []
    for root, _, filenames in os.walk(root_dir):
        for filename in fnmatch.filter(filenames, f"*.{extension}"):
            matches.append(Path(os.path.join(root, filename)))
    return matches

if __name__ == "__main__":
    args = sys.argv
    if len(args) == 2:
        asyncio.run(main(args[1]))
    else:
        print(len(args))
        print(args)
        raise RuntimeError("argument is not enough!!")

# パスは.leanファイルへのパスで指定