# Build using Dockerfile
```
docker build -t dreal4_test .
```

# Check size of the image
```
docker history dreal4_test
```

# Test it
```
docker run -it dreal4_test
```

# Tag it as dreal/dreal4
```
docker tag dreal4_test dreal/dreal4
```

# Push to dreal/dreal4 
```
docker push dreal/dreal4
```
