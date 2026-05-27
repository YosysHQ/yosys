set -e
set -x

# DEBUG: show python3 and python3-config outputs
if [ "$(uname)" != "Linux" ]; then
    # https://github.com/pypa/cibuildwheel/issues/2021
    ln -s $(dirname $(readlink -f $(which python3)))/python3-config $(dirname $(which python3))/python3-config
fi
python3 --version
python3-config --includes
