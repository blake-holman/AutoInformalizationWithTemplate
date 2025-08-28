import sys
import json
from pathlib import Path
from dataclasses import dataclass
from typing import List, Optional

@dataclass
class DependencyInfo:
    value : str
    dependencies : List[str]
@dataclass
class PriorityInfo:
    path : str
    level : int

class DependencyInfoEncoder(json.JSONEncoder):
    def default(self, o):
        if isinstance(o, DependencyInfo):
            return {'value': o.value, 'dependencies' : o.dependencies}
        return json.JSONEncoder.default(self, o)

def is_unnecessary_library_file(path : str)->bool:
    components = path.split("/")
    for component in components:
        if "Tactic" in component or "Mathport" in component:
            return True
    return False

def remove_unnecessary_library(info : DependencyInfo) -> Optional[DependencyInfo]:
    """
    TacticのインクルードとMathlib外のライブラリ参照を外す
    """
    if is_unnecessary_library_file(info.value):
        return None
    removed_target = []
    for dependency in info.dependencies:
        if not (dependency.startswith(".lake/packages/mathlib/Mathlib")) or is_unnecessary_library_file(dependency):
            removed_target.append(dependency)
    for target in removed_target:
        if target in info.dependencies:
            info.dependencies.remove(target)
    return info

def load_dependencies(path : Path)->List[DependencyInfo]:
    data = []
    with open(path, "r") as f:
        dependencies = json.load(f)
        for dependency in dependencies:
            path = dependency["value"].split("/premises/")[1]
            data.append(DependencyInfo(path, dependency["dependencies"]))
    return data
        
if __name__ == "__main__":
    args = sys.argv
    if len(args) == 2:
        pathObj = Path(args[1])
        data = load_dependencies(pathObj)
        preprocessed = []
        for datum in data:
            p = remove_unnecessary_library(datum)
            if p != None:
                preprocessed.append(p)
        js = json.dumps(preprocessed, cls=DependencyInfoEncoder)
        with open("dependencies_preprocessed.json", "w") as f:
            f.write(js)
        
        
