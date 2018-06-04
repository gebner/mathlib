pipeline {
  agent any
  stages {
    stage('build') {
      steps {
        sh "leanpkg test"
        sh "lean --recursive --export=mathlib.txt"
        sh "leanchecker mathlib.txt"
      }
    }
  }
}
