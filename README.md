# mTensor

Wolfram Engine과 C++로 구현한 인덱스를 갖는 텐서의 다양한 연산

# 사전 준비

이미 *Mathematica*가 설치되어 있다면 아래의 사전 준비는 필요 없다. 사실 주피터 노트북보다는 *Mathematica* 노트북 사용을 **추천**한다.

1. `Free Wolfram Engine for Developers` 다운로드 및 설치

    * [https://www.wolfram.com/engine/](https://www.wolfram.com/engine/)에서 다운로드
    * 적당한 폴더에 설치. 활성화를 위해 Wolfram ID 필요

2. 주피터 노트북 설치 ([아타콘다 파이썬](https://www.anaconda.com/products/individual) 추천)

3. 주피터 노트북을 위한 Wolfram Language kernel 설치

    * [저장소](https://github.com/WolframResearch/WolframLanguageForJupyter) 전체 압축을 다운로드
    * 압축을 푼 폴더에서 `.\configure-jupyter.wls add` 실행

# mTensor 설치

다운로드한 `mTensor.zip`을 `<Wolfram Engine 설치 폴더>/AddOns/Applications/`에 푼다.

* 만일 윈도우에서 MathLink 라이브러리 호출에 문제가 생기면 *Mathematica*가 제공하는 파일 `ml64i4.dll`을 파일 `xPermML64.mswin`이 있는 폴더인 `...\mTensor\xPermML\LibraryResources\`에 위치시킨다.

* 리눅스에서의 추가 설정

    - MathLink 라이브러리 호출을 위한 설정:

        > MLINKDIR=<mma_dir>/SystemFiles/Links/MathLink/DeveloperKit/Linux-x86-64/CompilerAdditions

        > export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$MLINKDIR

    - 실행 모드로 권한 설정:

        > chmod u+x <...>/mTensor/xPermML/LibraryResources/xPermML64.linux
