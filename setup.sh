git clone https://github.com/agda/agda
cd agda
  git checkout a5bd5a1
  git submodule update --init src/fix-whitespace
  stack --stack-yaml=stack-8.10.2.yaml build || exit -1
cd ..

git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib
  git checkout v1.5
  HERE=`pwd`
cd ..

echo "$HERE/standard-library.agda-lib" > .agda/libraries
