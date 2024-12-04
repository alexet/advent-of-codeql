import os
import json

# Iterate over years
for year in os.listdir('.'):
    if os.path.isdir(year):
        # check that it is not a hidden directory
        if year.startswith('.'):
            continue
        print(year)
        for day in os.listdir(os.path.join('.',year)):
            dayDir = os.path.join(year, day)
            if os.path.isdir(dayDir):
                print(dayDir)
                for name in ["real.in", "test.in"]:
                    file = os.path.join(dayDir, name)
                    if os.path.isfile(file):
                        print(file)
                        with open(file, 'r') as f:
                            data = f.read()
                            print(data)
                            baseName = os.path.splitext(name)[0]
                            contents = json.dumps({
                                "extensions":[
                                    {
                                        "addsTo":
                                        {
                                            'pack': "alexet/advent-of-code",
                                            'extensible' : baseName
                                        },
                                        "data":
                                        [[year, day, data]]
                                    }
                                ] 
                            })
                            print("Writing file: " + os.path.join(dayDir,baseName + ".yml"))
                            print(contents)
                            # Write the data file as a yml file
                            with open(os.path.join(dayDir,baseName + ".yml"), 'w') as f:
                                f.write(contents)

