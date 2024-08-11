#!/usr/bin/env bash

 : <<'BASH_MODULE_DOCS'
`scripts/import_trans_difference.sh <opt_commit1> <opt_commit2>` outputs a full diff of the
change of transitive imports in all the files between `<opt_commit1>` and `<opt_commit2>`.

If the commits are not provided, then it uses the current commit as `commit1` and
current `master` as `commit2`.

The output is of the form

|Files     |Import difference|
|-         |-                |
|Mathlib...| -34             |
  ...
|Mathlib...| 579             |

with collapsible tabs for file entries with at least 3 files.
BASH_MODULE_DOCS

if [ -n "${1}" ]
then
  commit1="${1}"
else
  commit1="$(git rev-parse HEAD)"
fi

if [ -n "${2}" ]
then
  commit2="${2}"
else
  commit2="$(git merge-base master ${commit1})"
fi

#printf 'commit1: %s\ncommit2: %s\n' "$commit1" "$commit2"

currCommit="$(git rev-parse HEAD)"

getTransImports () {
  python3 scripts/count-trans-deps.py Mathlib |
    # produce lines of the form `Mathlib.ModelTheory.Algebra.Ring.Basic,-582`
    sed 's=\([0-9]*\)[},]=,'"${1}"'\1\n=g' |
    tr -d ' "{}:'
}

formatGitDiff () {
  local new=new
  local removed=removed
  local swap='s=,R[0-9]*,\(.*\)=, (paired with `\1`)='
  if [ -n "${2}" ]
  then
    new=removed
    removed=new
    swap='s=^\([^,]*\),,R[0-9]*,\(.*\)=\2,, (paired with `\1`)='
  fi
  git diff --name-status "${1}" |
    awk -F'\t' '!($1 == "M") {
      printf("%s,,%s%s\n", $NF, $1, NF == 2? "" : ","$2)
    }' |
    sed '
      s=/=.=g
      s=\.lean,=,=
      s=,A=, ('"${new}"' file)=
      s=,D=, ('"${removed}"' file)=
      '"${swap}"'
    '
}

getFormattedTransImports () {
  { getTransImports
    formatGitDiff "${1}" "${2}"; } |
    awk -F, '
         ($2+0 == $2) { record[$1]=$2; if(name[$1] == "") { name[$1]="`"$1"`" } }
         ($2 == "")   { name[$1]="`"$1"`"$3 }
      END {
        for(fil in name)
        { printf("%s,%s\n", name[fil], record[fil]+0) }
      }'
}

git checkout "${commit1}"
git checkout master scripts/count-trans-deps.py
getTransImports > transImports1.txt
#getFormattedTransImports "${commit2}" > transImports1.txt
git checkout "${currCommit}"

git checkout "${commit2}"
git checkout master scripts/count-trans-deps.py
getTransImports > transImports2.txt
#getFormattedTransImports "${commit1}" rev > transImports2.txt
git checkout "${currCommit}"

importsDifferences () {
  awk -F, '{ diff[$1]+=$2 } END {
    con=0
    for(fil in diff) {
      if(!(diff[fil] == 0)) { printf("%s,%s\n", fil, diff[fil]) }
    }
  }' transImports*.txt
}

addGitInfo () {
(
  importsDifferences
  #getTransImports #| grep "Topology\.Shea"
  git diff --name-status "${commit2}".."${commit1}" |
    awk '/^[^M]/{
      gsub(/\//, ".")
      gsub(/\.lean/, "")
      printf("%s,,%s\n", $NF, $(NF-1))
      if(NF == "3") {printf("%s,rev,%s\n", $(NF-1), $NF)}
    }'
) |
  awk -F, '
    (NF == 2) { imports[$1]=$2 }
    (NF == 3) { status[$1]=$3; if($2 == "rev") { rename[$3]=$1 } }
    END {
      for(fil in imports) {
        if (fil in rename) { stat=sprintf(" (was called `%s`)", status[fil]) }
        else if (status[fil] == "A") { stat=" (new file)" }
        else if (status[fil] == "D") { stat=" (deleted file)" }
        else if (status[fil] == "") { stat="" }
        else { stat=sprintf(" (became `%s`)", status[fil]) }
        printf("`%s`%s,%s\n", fil, stat, imports[fil])
      }
    }'
}

git diff --name-status "${commit2}".."${commit1}" |
  awk '/^[^M]/{ gsub(/\//, "."); gsub(/\.lean/, ""); printf("%s,,%s\n", $NF, $(NF-1))}'

printf '\n\n<details><summary>Import changes for all files</summary>\n\n%s\n\n</details>\n' "$(
  printf "|Files|Import difference|\n|-|-|\n"
  (awk -F, '{ diff[$1]+=$2 } END {
    con=0
    for(fil in diff) {
      if(!(diff[fil] == 0)) {
        con++
        nums[diff[fil]]++
        reds[diff[fil]]=reds[diff[fil]]" "fil
      }
    }
    if (10000 <= con) { printf("There are %s files with changed transitive imports: this is too many to display!\n", con) } else {
      for(x in reds) {
        if (nums[x] <= 2) { printf("|%s|%s|\n", reds[x], x) }
        else { printf("|<details><summary>%s files</summary>%s</details>|%s|\n", nums[x], reds[x], x) }
      }
    }
  }' transImports*.txt | sort -t'|' -n -k3 | grep "ew"
  ))"

printf 'formatGitDiff %s\n' "${commit1}" &&
formatGitDiff "${commit1}" &&
printf 'formatGitDiff %s\n' "${commit2}" &&
formatGitDiff "${commit2}"
head -50 transImports1.txt



printf '\n\n<details><summary>Import changes for all files</summary>\n\n%s\n\n</details>\n' "$(
  printf "|Files|Import difference|\n|-|-|\n"
  (addGitInfo | awk -F, '{ diff[$1]+=$2 } END {
    con=0
    for(fil in diff) {
      if(!(diff[fil] == 0)) {
        con++
        nums[diff[fil]]++
        reds[diff[fil]]=reds[diff[fil]]" "fil
      }
    }
    if (10000 <= con) { printf("There are %s files with changed transitive imports: this is too many to display!\n", con) } else {
      for(x in reds) {
        if (nums[x] <= 2) { printf("|%s|%s|\n", reds[x], x) }
        else { printf("|<details><summary>%s files</summary>%s</details>|%s|\n", nums[x], reds[x], x) }
      }
    }
  }' | sort -t'|' -n -k3 | grep "ew"
  ))"
