python -m venv informalize_venv
if echo "$(uname -s)" | grep -q "MINGW64_NT"; then
    . informalize_venv/Scripts/activate
else
    . informalize_venv/bin/activate
fi
pip install -U pip
pip install -r requirements.txt