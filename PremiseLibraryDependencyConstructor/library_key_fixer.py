import json

def add_lean_suffix(data):
    def process_dict(d):
        updated = {}
        for key, value in d.items():
            if isinstance(value, dict):
                for k, v in value.items():
                    if isinstance(v, dict):
                        if "description" in v:
                            new_key = f"{key}.lean"
                            updated[new_key] = value
                        else:
                            updated[key] = process_dict(value) 
                    else:
                        updated[key] = value
            else:
                updated[key] = value
        return updated

    return process_dict(data)

if __name__ == "__main__":
    with open("premise_library.json", "r", encoding="utf-8") as f:
        data = json.load(f)
    updated = add_lean_suffix(data)
    with open("premise_lib.json", "w", encoding="utf-8") as f:
        json.dump(updated, f, ensure_ascii=False, indent=2)
    
