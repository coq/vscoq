# Release process

1. Make sure that `CHANGELOG.md` is up to date
2. Update the version number in package.json
3. Publish using vsce:
   ```
   vsce login maximedenes
   vsce publish
   ```
