# mTensor

Wolfram Engine과 C++로 구현한 인덱스 텐서 연산

# 사전 준비

1. `Free Wolfram Engine for Developers` 다운로드 및 설치

    * [Wolfram Engine](https://www.wolfram.com/engine/)에서 다운로드
    * 적당한 폴더에 설치. 활성화를 위해 Wolfram ID 필요

2. 주피터 노트북 설치 ([아타콘다 파이썬](https://www.anaconda.com/products/individual) 추천)

3. 주피터 노트북을 위한 Wolfram Language kernel 설치

    * [저장소](https://github.com/WolframResearch/WolframLanguageForJupyter) 전체 압축을 다운로드
    * 압축을 푼 폴더에서 `.\configure-jupyter.wls add` 실행

# mTensor 설치

mTensor.zip을 <Wolfram Engine 설치 폴더>/AddOns/Applications/mTensor에 풀기
(또는 <Wolfram Engine 설치 폴더>/Configuration/Kernel/init.m에 압축을 푼 폴더를 $Path로 등록)
