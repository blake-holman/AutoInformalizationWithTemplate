import json
import os
from pathlib import Path

"""
premise_libファイルが大きすぎるので適切なサイズにデータを分割する

"""
if __name__ == "__main__":
    library_files_dir = Path("Library")
    if not os.path.exists(library_files_dir):
        os.mkdir(library_files_dir)
    with open("premise_lib.json", "r", encoding="utf-8") as f:
        data = json.load(f)
    for top_key in data.keys():
        dirpath = library_files_dir.joinpath(top_key)
        if not os.path.exists(dirpath):
            os.mkdir(dirpath)
        for domain_key in data[top_key].keys():
            domain_data = data[top_key][domain_key]
            with open(dirpath.joinpath(domain_key + ".json"), "w", encoding="utf-8") as f:
                json.dump(domain_data, f, ensure_ascii=False, indent=2)