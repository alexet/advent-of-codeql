import os
import json

# Iterate over direct subdirectories
for root, dirs, files in os.walk('.'):
    for file in files:
        if file.endswith('.in'):
            print("Processing file: " + os.path.join(root,file))
            with open(os.path.join(root,file), 'r') as f:
                # Read the whole file into a string
                data = f.read()
                                # Create filename without extension
                baseName = os.path.splitext(file)[0]
                # Create the data file
                contents = json.dumps({
                    "extensions":[
                        {
                            "addsTo":
                             {
                                 'pack': "alexet/advent-of-code",
                                 'extensible' : baseName
                             },
                            "data":
                            [[data]]
                        }
                    ] 
                })
                print("Writing file: " + os.path.join(root,baseName + ".yml"))
                print(contents)
                # Write the data file as a yml file
                with open(os.path.join(root,baseName + ".yml"), 'w') as f:
                    f.write(contents)

