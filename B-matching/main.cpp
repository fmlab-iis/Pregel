//
//  main.cpp
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

struct Vertex {
    long vertexID;
    int capacity;
} Vertex;

struct Edge {
    long srcID, destinID;
    int attr;
} Edge;

vector<struct Vertex> v;
vector<struct Edge> e;
vector<struct Edge> combination;

long sumOfWeight = 0;

void check(vector<struct Edge> comb,  string argv1,string argv2,string argv3,string argv4, string argv5) {
    vector<struct Vertex> check_v;
    check_v = v;
    long tmp_max = 0;
    for(int i = 0; i<comb.size(); i++){
        //cout<< "src: "<< comb[i].srcID<< ", dest: "<< comb[i].destinID<< ", atr: "<< comb[i].attr<< endl;
        
        check_v[comb[i].srcID].capacity--;
        check_v[comb[i].destinID].capacity--;
        
        if(check_v[comb[i].srcID].capacity == -1 || check_v[comb[i].destinID].capacity == -1){
            //cout<< "----------"<<endl;
            return;
        }else{
            tmp_max += comb[i].attr;
        }
    }
    if(tmp_max > sumOfWeight){
        sumOfWeight = tmp_max;

        ofstream file;
        file.open("./"+argv1+"-"+argv2+"-"+argv3+"-"+argv4+"-"+argv5+"-boutput.txt",ios_base::out);


        for(int i = 0; i<comb.size(); i++){
            file<< "Edge("<< comb[i].srcID<< ","<< comb[i].destinID<< ","<< comb[i].attr<<")"<<endl;
        }
    }
    //cout<< "-------"<<tmp_max<<"-------"<<endl;
}


void go(int offset, int k, string argv1,string argv2,string argv3,string argv4, string argv5) {
    if (k == 0) {
        check(combination, argv1, argv2, argv3, argv4, argv5);
        return;
    }
    for (int i = offset; i <= e.size() - k; ++i) {
        combination.push_back(e[i]);
        go(i+1, k-1, argv1, argv2, argv3, argv4, argv5);
        combination.pop_back();
    }
}

int main(int argc,char *argv[])
{
    string argv1(argv[1]);
    string argv2(argv[2]);
    string argv3(argv[3]);
    string argv4(argv[4]);
    string argv5(argv[5]);


        string se = "./"+argv1+"-"+argv2+"-"+argv3+"-"+argv4+"-"+argv5+"-edge.txt";
        ofstream file;
        file.open(se,ios_base::out);
        file.close();
        file.open("./"+argv1+"-"+argv2+"-"+argv3+"-"+argv4+"-"+argv5+"-vertex.txt",ios_base::out);
        file.close();
        
        int vertexNum = atoi(argv[1]);
        int maxCapacity = atoi(argv[2]);
        
        unsigned seed;
        seed = (unsigned)time(NULL);
        srand(seed);
        
        struct Vertex tmp;
        tmp.vertexID = 0;
        tmp.capacity = -1;
        v.push_back(tmp);
        
        file.open("./"+argv1+"-"+argv2+"-"+argv3+"-"+argv4+"-"+argv5+"-vertex.txt",ios_base::app);
        
        for(int i = 1; i <= vertexNum ; i++){

            tmp.vertexID = i;
            tmp.capacity = (rand() % maxCapacity) + 1;
            
            v.push_back(tmp);
            
            file << tmp.vertexID << " " << tmp.capacity << endl;
            
            
            //cout<< i <<" "<< v[i].capacity <<endl;
        }
        
        file.close();
        
        int maxWeight = atoi(argv[3]);
        int alpha = atoi(argv[4]);
        
        file.open("./"+argv1+"-"+argv2+"-"+argv3+"-"+argv4+"-"+argv5+"-edge.txt",ios_base::app);
        
        for(int i = 1; i <= vertexNum; i++){
            for(int j = i; j <= vertexNum; j++){
                if(i == j) continue;
                else {
                    if(rand() % alpha == 1){
                        
                        struct Edge tmp;
                        tmp.srcID = i;
                        tmp.destinID = j;
                        tmp.attr = (rand() % maxWeight) + 1;
                        
                        e.push_back(tmp);
                        
                        file << tmp.srcID << " " << tmp.destinID  << " " << tmp.attr << endl;
                        
                        
                    }else{
                        continue;
                    }
                }
            }
        }
        
        file.close();
        
        for(int i = 1; i < e.size(); i++){
            go(1, i, argv1, argv2, argv3, argv4, argv5);
        }
        
        file.open("./"+argv1+"-"+argv2+"-"+argv3+"-"+argv4+"-"+argv5+"-bresult.txt",ios::out);
        file << sumOfWeight << endl;
        file.close();
    
    return 0;
}
