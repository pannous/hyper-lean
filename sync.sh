echo ⚠️ this file is hard linked across several projects
echo occasionally check if they are in sync
diff ~/Documents/notes/hyperreals.md ~/dev/apps/wasp/wiki/hyperreals.md 
diff ~/Documents/notes/hyperreals.md ~/dev/script/lean4/hyper/Readme.md 
echo ⚠️ if not in sync, re-link hard:
ln ~/Documents/notes/hyperreals.md ~/dev/apps/wasp/wiki/hyperreals.md 
ln ~/Documents/notes/hyperreals.md ~/dev/script/lean4/hyper/Readme.md 