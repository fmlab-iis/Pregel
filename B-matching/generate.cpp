//
//  generate.cpp
//  graph
//
//  Created by Dreamcastle on 2016/8/1.
//  Copyright © 2016年 Dreamcastle. All rights reserved.
//

#include <iostream>
#include <fstream>
#include <vector>
#include <string>

using namespace std;

int main(int argc,char *argv[])
{
    string argv1(argv[1]);
    int num = atoi(argv[2]);
    int vertNum = atoi(argv[1]);
    int size = atoi(argv[3]);

    unsigned seed;
    seed = (unsigned)time(NULL);
    srand(seed);

    ofstream file;
    file.open("parameters.txt",ios_base::out);

    for(int i = 0; i < num ; i++){
        for(int j = 0; j < size ; j++){
            file << argv1 << " " << (rand() % (vertNum-6)) + 5 << " " << (rand() % 300) + 200 << " " << (rand() % 3) + 2 << " " << j << endl;
        }
    }



    
    return 0;
}
