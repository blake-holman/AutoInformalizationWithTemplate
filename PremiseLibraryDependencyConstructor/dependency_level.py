import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict
import json

@dataclass
class DependencyInfo:
    value : str
    dependencies : List[str]
@dataclass
class PriorityInfo:
    path : str
    level : int

class PriorityInfoEncoder(json.JSONEncoder):
    def default(self, o):
        if isinstance(o, PriorityInfo):
            return {'path': o.path, 'level' : o.level}
        return json.JSONEncoder.default(self, o)

def load_dependencies(path : Path)->List[DependencyInfo]:
    data = []
    with open(path, "r") as f:
        dependencies = json.load(f)
        for dependency in dependencies:
            data.append(DependencyInfo(dependency["value"], dependency["dependencies"]))
    return data
def calculate_level(data : List[DependencyInfo]) -> List[PriorityInfo]:
    library_levels : Dict[str, int] = {}
    # 依存ファイルがないものを最高レベルとしておく
    removed = []
    for datum in data:
        if datum.dependencies == []:
            removed.append(datum)
            library_levels[datum.value] = 1
    for target in removed:
        data.remove(target)
    loop_count = 0
    while len(data) != 0 and loop_count < 100000000:
        removed = []
        for datum in data:
            isLevelConfigurable = True
            levels = []
            for dependency in datum.dependencies:
                if not dependency in library_levels.keys():
                    isLevelConfigurable = False
                    break
                levels.append(library_levels[dependency])
            if isLevelConfigurable:
                removed.append(datum)
                if not datum.value in library_levels.keys():
                    library_levels[datum.value] = max(levels) + 1
        for target in removed:
            data.remove(target)
        print(f"Progress : {len(data)}")
        loop_count += 1
    if loop_count == 100000000:
        raise RuntimeError("ロジックに誤りあり？")
    priorities = []
    for key, value in library_levels.items():
        priorities.append(PriorityInfo(key, value))
    return priorities


if __name__ == "__main__":
    args = sys.argv
    if len(args) == 2:
        pathObj = Path(args[1])
        data = load_dependencies(pathObj)
        priorities = calculate_level(data)
        js = json.dumps(priorities, cls=PriorityInfoEncoder)
        with open("dependency_levels.json", "w") as f:
            f.write(js)
        