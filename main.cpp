#include <cmath>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include "./rtree/rtree.h"
#include "./rtree/rtnode.h"
#include "./rtree/entry.h"
#include "./blockfile/blk_file.h"
#include "./blockfile/cache.h"
#include "./linlist/linlist.h"
#include "./rtree/rtree_cmd.h"
#include <time.h>
#include <iostream>
#include "rand.h"
#include <string>  
#include<sstream>
#include<algorithm>


#include "cdf.h"

#include <fstream>
#include <vector>
#include <map>


using namespace std;
using std::cout;

//const int pvtCntMax = 3;// the maximal number of pivots for a single attribute
//const int CDDNodeSize = 1000;
struct CDD_Node {
	int ID;//ID starts from 0
	int determinant_attribute; // in [1, dimension]
	vector<double> cv;
	//double cv[pvtCntMax * 2] = { 1, 0, 1, 0, 1, 0};// intervals of constraint values
	double ci = 0; // constraint interval
	double di = 0; // dependent interval
	vector<int> CDDID;// CDD ID starts from 0
};

struct R_Node {
	int nodeID = -1; //the node ID in the R*-tree; this ID parameter is not required to be refilled; for the purpose of double-check
	bool key_exist = false;
	vector<vector<double>> distItv;// the interval of distances between attribute values and pivots on each attribute; initialized as pairs {1, 0}
	vector<vector<int>> tokenSizeItv;// the interval of token sizes of attribute values on each attribute; intialalized as pairs {100000, 0}
};

struct Grid_Cell {
	int cell_ID = -1; // this id not required, only for debug purpose
	vector<double> main_distItv; // this is to record the the interval of this cell on each dimension; contains 2 * dimension values; based only on main attribute pivots
	vector<int> IDs_Keyword; // the set of data IDs that contain at least one keyword in the keyword lists; contains keyword-related objects if size() > 1
	vector<int> IDs; // the set of data in this cell
	vector<vector<double>> distItv; // based on main and minor attribute pivots; based on imputed values inside
	vector<vector<int>> tokenSizeItv;
};

struct Data {
	int ID;// the position in the data stream
	string actual_ID; // the real ID in real world
	vector<string> attributes;
};

struct Instance {
	int ID;
	vector<string> attributes;
	int frequency;
};

struct Imputed_Data {
	bool imputed_complete = false;
	bool is_incomplete = false;
	int ID; // the position in data stream; start from 0
	string actual_ID; // the actual ID of this data object
	int iDS_n; // which data stream ([1, n]) this object from 
	bool key_exist = false;
	vector<vector<int>> matched_entities; // the set of object IDs (from other data streams) matched with this object
	vector<vector<string>> possible_values; // all possible values on d attributes
	vector<vector<int>> value_frequency; // the frequencies of possible values on d attributes
	vector<vector<double>> distItv;
	vector<vector<int>> tokenSizeItv;
	vector<double> expectations; // expectations on d dimension; only consider main attribute pivot for each dimension
	//vector<double> lb_expectations;
	//vector<double> ub_expectations;
	vector<Instance> obj_instances;
};

struct CDD_Rules {
	int value_attribute; // in [1, dimension], determinant attribute with specific values as constraints
	int interval_attribute;// in [1, dimension], determinant attribute with intervals as constraint
	int Aj_attribute; // in [1, dimension], dependent attribute
	vector<string> Ax_values;
	double Ax_interval;
	vector<double> Aj_interval;
};

struct Attribute_Pivots {
	int attribute; // in [1, dimension], on which attribute these pivots for
	vector<string> att_pivs; // contains main (att_pivs.at(0)) and minor attribute pivots
};

struct Matching_Record {
	vector<string> actual_ID;
	vector<int> iDS_n;
};

struct Parameter_Setting {// only need one instantiation
	int file_cnt;
	double alpha;// probabilistic threshold for ER matching
	double gamma; // distance threshold
	int dimension;
	int repository_size;// the size of data repository R
	double xi; // the missing rate, valid in [0, 1]
	vector<int> missing_attributes; // the ID (1-dimension) of missing attributes
	vector<bool> is_digits; // is digit value on each dimensions
	vector<vector<CDD_Rules>> CDDs;
	int pvtCntMax;// the maximal number of pivots for a single attribute
	int CDDNodeSize;
	int parSize;
	double entropyMin;
	double cell_length;
	double R_ratio;
	//vector<vector<int>> determinant_attributes; // determinant attributes for each dimension; 
												// for each vector<int>, it contains two attribute IDs: first takes determinant interval as constraint, second takes specific values as intervals
	//vector<vector<string>> v_domains; // the value domain of attributes
	double Ax_interval; // for simplicity, in this implementation, we use the same determinant interval for all CDD rules
	//vector<vector<double>> Aj_intervals; // the intervals of dependent attributes
	//vector<vector<string>> attribute_pivots;
	vector<vector<Attribute_Pivots>> attribute_pivots;
	vector<string> keywords;// the set of related keywords
	int object_max_size;
	int Wt_size;
	double Wt_rate; //ratio responding to file size
	//bool is_CDDs_generated = false;
	//bool is_pivots_generated = false;
	vector<string> stream_paths;
	vector<string> pivot_paths;
	vector<string> CDD_paths;
	vector<string> converted_file_paths;
	vector<string> tree_file_paths;
	vector<RTree*> tree_roots;
	string ER_result_path;
	vector<string> ground_truth_paths;
	string quality_evaluation_path;
	int method_ID = -1;
};


double Jaccard_Similarity(string A1, string A2) {
	double sim_score = 0;
	vector<string> A1_ss;
	vector<string> A2_ss;
	int v_size1, v_size2;

	istringstream iss1, iss2;
	iss1.str(A1);
	iss2.str(A2);

	string token_tmp;

	do {
		iss1 >> token_tmp;
		if (!iss1.fail()) {
			A1_ss.push_back(token_tmp);
		}
	} while (!iss1.fail());
	v_size1 = A1_ss.size();

	do {
		iss2 >> token_tmp;
		if (!iss2.fail()) {
			A2_ss.push_back(token_tmp);
		}

	} while (!iss2.fail());
	v_size2 = A2_ss.size();

	int common_cnt = 0;
	if (v_size1 <= v_size2) {
		for (int it = 0; it < v_size1; it++) {
			for (int it2 = 0; it2 < v_size2; it2++) {
				if (A1_ss.at(it).find(A2_ss.at(it2)) != std::string::npos || A2_ss.at(it2).find(A1_ss.at(it)) != std::string::npos) {
					common_cnt++;
					break;
				}
			}
		}
	}
	else {
		for (int it = 0; it < v_size2; it++) {
			for (int it2 = 0; it2 < v_size1; it2++) {
				if (A2_ss.at(it).find(A1_ss.at(it2)) != std::string::npos || A1_ss.at(it2).find(A2_ss.at(it)) != std::string::npos) {
					common_cnt++;
					break;
				}
			}
		}
	}
		
	sim_score = (double)common_cnt / (v_size1 + v_size2 - common_cnt);
	return sim_score;

	
	/*
	vector<bool> is_founded;
	for (int it = 0; it < v_size2; it++) {
		is_founded.push_back(false);
	}

	int common_cnt = 0;

	for (int it1 = 0; it1 < v_size1; ++it1) {
		for (int it2 = 0; it2 < v_size2; ++it2) {
			if (!is_founded.at(it2) && A1_ss.at(it1).compare(A2_ss.at(it2)) == 0) {
				++common_cnt;
				is_founded.at(it2) = true;
			}

		}
	}

	sim_score = (double)common_cnt / (v_size1 + v_size2 - common_cnt);
	return sim_score;
	*/
}

double Jaccard_Distance(string A1, string A2) {
	double dist_score;

	if (A1.empty() || A2.empty())//currently, we use this easy for dealing with data sets which originally contain missing attributes
		dist_score = 0.5;
	else
		dist_score = 1 - Jaccard_Similarity(A1, A2);

	return dist_score;
}

bool Jaccard_Sim_obj(Imputed_Data object1, Imputed_Data object2, Parameter_Setting& p_setting) {// this function is revoked after the function norm_numeric; ER compare without pruning
	bool is_matched;
	//double Jaccard_score = 0;
	double instance_Jaccard_score = 0;
	double ER_matching_prob = 0;
	string A1, A2;
	vector<string> object1_instance;
	vector<string> object2_instance;

	int object1_instance_cnt = 1;
	int object2_instance_cnt = 1;

	for (int it = 0; it <= p_setting.missing_attributes.size(); it++) {//obtain the instance number of imputed object object1
		int possible_value_cnt = 0;
		int d = p_setting.missing_attributes.at(it);
		for (int it2 = 0; it2 < object1.value_frequency.at(d - 1).size(); it2++) {
			possible_value_cnt = possible_value_cnt + object1.value_frequency.at(d - 1).at(it2);
		}
		object1_instance_cnt = object1_instance_cnt * possible_value_cnt;
	}

	for (int it = 0; it <= p_setting.missing_attributes.size(); it++) {
		int possible_value_cnt = 0;
		int d = p_setting.missing_attributes.at(it);
		for (unsigned it2 = 0; it2 < object2.value_frequency.at(d - 1).size(); it2++) {
			possible_value_cnt = possible_value_cnt + object2.value_frequency.at(d - 1).at(it2);
		}
		object2_instance_cnt = object2_instance_cnt * possible_value_cnt;
	}

	int total_base_cnt = object1_instance_cnt * object2_instance_cnt;

	//vector<Instance> object1_instances = obtain_instances(object1, p_setting);
	//vector<Instance> object2_instances = obtain_instances(object2, p_setting);
	vector<Instance> object1_instances, object2_instances;
	for (int it = 0; it < object1.obj_instances.size(); it++) {
		object1_instances.push_back(object1.obj_instances.at(it));
	}

	for (int it = 0; it < object2.obj_instances.size(); it++) {
		object2_instances.push_back(object2.obj_instances.at(it));
	}

	for (int it = 0; it < object1_instances.size(); it++) {
		Instance instance1 = object1_instances.at(it);
		for (int it2 = 0; it2 < object2_instances.size(); it2++) {
			Instance instance2 = object2_instances.at(it2);
			instance_Jaccard_score = 0;
			for (int d = 1; d <= p_setting.dimension; d++) {
				A1 = instance1.attributes.at(d - 1);
				A2 = instance2.attributes.at(d - 1);
				if (!p_setting.is_digits.at(d - 1)) {
					instance_Jaccard_score += Jaccard_Similarity(A1, A2);
				}
				else {
					instance_Jaccard_score += 1 - abs(stod(A1) - stod(A2));
				}
			}
			if (instance_Jaccard_score > p_setting.gamma) {
				ER_matching_prob = ER_matching_prob + (double)(instance1.frequency * instance2.frequency) / total_base_cnt;
			}
		}
	}

	if (ER_matching_prob > p_setting.alpha)
		is_matched = true;
	else
		is_matched = false;

	return is_matched;
}

double obtain_Aj_interval(vector<vector<Data>> objects, int iDS_n, int determinant_att, int dependent_att, Parameter_Setting p_setting) {// Given a determinant attribute, this method returns the interval on dependent attribute
	//double Ax_interval = 1 - p_setting.gamma / p_setting.dimension;// a determined interval based on dimension and gamma (a special case)
	double Ax_interval = p_setting.Ax_interval;
	double Aj_interval = 0;
	string Ax1, Ax2, Aj1, Aj2;
	double X_distance, Aj_distance, d_Ax1, d_Ax2, d_Aj1, d_Aj2;

	for (int i = 0; i < objects.at(iDS_n - 1).size(); i++) {
		Ax1 = objects.at(iDS_n - 1).at(i).attributes.at(determinant_att - 1);
		Aj1 = objects.at(iDS_n - 1).at(i).attributes.at(dependent_att - 1);

		if (p_setting.is_digits.at(determinant_att - 1)) {
			d_Ax1 = stod(Ax1);
		}

		if (p_setting.is_digits.at(dependent_att - 1)) {
			d_Aj1 = stod(Aj1);
		}

		for (int j = i + 1; j < objects.at(iDS_n - 1).size(); j++) {
			Ax2 = objects.at(iDS_n - 1).at(j).attributes.at(determinant_att - 1);
			if (p_setting.is_digits.at(determinant_att - 1)) {
				d_Ax2 = stod(Ax2);
				X_distance = abs(d_Ax1 - d_Ax2);
			}
			else {
				X_distance = Jaccard_Distance(Ax1, Ax2);
			}
			if (X_distance <= Ax_interval) {
				Aj2 = objects.at(iDS_n - 1).at(j).attributes.at(dependent_att - 1);
				if (p_setting.is_digits.at(dependent_att - 1)) {
					d_Aj2 = stod(Aj2);
					Aj_distance = abs(d_Aj1 - d_Aj2);
				}
				else {
					Aj_distance = Jaccard_Distance(Aj1, Aj2);
				}
				if (Aj_distance > Aj_interval) {
					Aj_interval = Aj_distance;
				}
			}
		}
	}

	return Aj_interval;
}

vector<Instance> obtain_instances(Imputed_Data object, Parameter_Setting& p_setting) {// we assume there are at most 3 missing attributes
	vector<Instance> instances;
	Instance single_instance;
	string non_initialized;
	for (int dim = 1; dim <= p_setting.dimension; dim++)
		single_instance.attributes.push_back(non_initialized);

	if (p_setting.missing_attributes.size() == 1) {// only 1 missing attribute
		int dim1 = p_setting.missing_attributes.at(0);
		for (int it = 0; it < object.possible_values.at(dim1 - 1).size(); it++) {
			//single_instance.attributes.clear();
			single_instance.ID = it;
			single_instance.attributes.at(dim1 - 1) = object.possible_values.at(dim1 - 1).at(it);
			single_instance.frequency = object.value_frequency.at(dim1 - 1).at(it);
			for (int d = 1; d <= p_setting.dimension; d++) {
				if (d != dim1) {
					single_instance.attributes.at(d - 1) = object.possible_values.at(d - 1).at(0);
				}
			}
			instances.push_back(single_instance);
		}
	}

	if (p_setting.missing_attributes.size() == 2) { // for the case of 2 missing attribute values
		int dim1 = p_setting.missing_attributes.at(0);
		int dim2 = p_setting.missing_attributes.at(1);
		for (int it = 0; it < object.possible_values.at(dim1 - 1).size(); it++) {
			for (int it2 = 0; it2 < object.possible_values.at(dim2 - 1).size(); it2++) {
				//single_instance.attributes.clear();
				single_instance.ID = it * object.possible_values.at(dim2 - 1).size() + it2;
				single_instance.attributes.at(dim1 - 1) = object.possible_values.at(dim1 - 1).at(it);
				single_instance.attributes.at(dim2 - 1) = object.possible_values.at(dim2 - 1).at(it2);
				single_instance.frequency = object.value_frequency.at(dim1 - 1).at(it) * object.value_frequency.at(dim2 - 1).at(it2);
				for (int d = 1; d <= p_setting.dimension; d++) {
					if (d != dim1 && d != dim2) {
						single_instance.attributes.at(d - 1) = object.possible_values.at(d - 1).at(0);
					}
				}
				instances.push_back(single_instance);
			}
		}
	}

	if (p_setting.missing_attributes.size() == 3) { // for the case of 3 missing attribute values
		int dim1 = p_setting.missing_attributes.at(0);
		int dim2 = p_setting.missing_attributes.at(1);
		int dim3 = p_setting.missing_attributes.at(2);
		for (int it = 0; it < object.possible_values.at(dim1 - 1).size(); it++) {
			for (int it2 = 0; it2 < object.possible_values.at(dim2 - 1).size(); it2++) {
				for (int it3 = 0; it3 < object.possible_values.at(dim3 - 1).size(); it3++) {
					//single_instance.attributes.clear();
					single_instance.ID = it * (object.possible_values.at(dim2 - 1).size() * object.possible_values.at(dim3 - 1).size())
						+ it2 * (object.possible_values.at(dim3 - 1).size()) + it3;
					single_instance.attributes.at(dim1 - 1) = object.possible_values.at(dim1 - 1).at(it);
					single_instance.attributes.at(dim2 - 1) = object.possible_values.at(dim2 - 1).at(it2);
					single_instance.attributes.at(dim3 - 1) = object.possible_values.at(dim3 - 1).at(it3);
					single_instance.frequency = object.value_frequency.at(dim1 - 1).at(it) * object.value_frequency.at(dim2 - 1).at(it2) * object.value_frequency.at(dim3 - 1).at(it3);
					for (int d = 1; d <= p_setting.dimension; d++) {
						if (d != dim1 && d != dim2 && d != dim3) {
							single_instance.attributes.at(d - 1) = object.possible_values.at(d - 1).at(0);
						}
					}
					instances.push_back(single_instance);
				}
			}
		}
	}

	return instances;
}

int token_size(string sentence) {// this function is to calculate the number of words in a sentence; only for string parameter
	int size = 0;
	char emptyC = ' ';
	bool counted = false;
	for (int i = 0; i < sentence.length(); i++) {
		while (sentence.at(i) != emptyC) {
			if (!counted) {
				size++;
				counted = true;
			}
			if (i >= sentence.length() - 1) {
				break;
			}

			i++;
		}
		counted = false;
	}

	return size;
}

vector<int> missing_IDs(int count, double xi) {
	vector<int> IDs;
	int missing_cnt = floor(count * xi);
	srand(time(nullptr)); // giving random number generator

	int generatedNumber;

	//for (int it = 200; it < 400; it++)
	//	IDs.push_back(it);
	
	
	while (IDs.size() < missing_cnt) {
		generatedNumber = rand() % count;
		bool is_exist = false;
		for (int mcnt = 0; mcnt < IDs.size(); mcnt++) {
			if (IDs.at(mcnt) == generatedNumber) {
				is_exist = true;
				break;
			}
		}
		if (!is_exist)
			IDs.push_back(generatedNumber);
	}
	

	return IDs;
}

int obtain_object_size(Parameter_Setting& p_setting) {
	int object_size = 10000000;
	for (int it = 0; it < p_setting.stream_paths.size(); it++) {
		ifstream in(p_setting.stream_paths.at(it));
		string line;
		int current_size = 0;
		if (in)
		{
			while (getline(in, line))
			{
				current_size++;
			}
		}
		else
		{
			std::cout << "no such file" << endl;
		}

		if (current_size < object_size)
			object_size = current_size;

		in.close();
	}

	return object_size;
}

vector<vector<Data>> load_R(Parameter_Setting& p_setting) {// we assume the n data streams have the same dimensionality 
	vector<vector<Data>> data_stream;
	vector<Data> single_data_stream;
	for (int it = 0; it < p_setting.stream_paths.size(); it++) {
		single_data_stream.clear();
		ifstream in(p_setting.stream_paths.at(it));

		string line, attribute;
		int attribute_cnt;
		int object_cnt = 0;

		istringstream iss;

		if (in)
		{
			while (getline(in, line))
			{
				iss.clear();
				iss.str(line);
				attribute_cnt = 0;// the number of retrieved attributes

				Data object;
				object.ID = object_cnt;

				while (getline(iss, attribute, ',')) {
					if (attribute_cnt >= p_setting.dimension + 1)
						break;

					if (attribute_cnt == 0)// the first attribute is entity ID
					{
						object.actual_ID = attribute;
					}
					else {
						if (attribute == "")
							attribute = "null";
						object.attributes.push_back(attribute);
					}
						
					attribute_cnt++;
				}

				if (attribute_cnt > 0) {
					for(int it2 = attribute_cnt; it2 <= p_setting.dimension; it2++)
						object.attributes.push_back("null");
					single_data_stream.push_back(object);
					object_cnt++;
				}
				if (object_cnt >= p_setting.object_max_size)
					break;
			}
			if (object_cnt > 0)
				data_stream.push_back(single_data_stream);
		}
		else
		{
			std::cout << "no such file" << endl;
		}

		in.close();
	}

	return data_stream;
}

vector<vector<Data>> obtain_data_repository(vector<vector<Data>> all_data, Parameter_Setting& p_setting) {
	vector<vector<Data>> data_repository;
	vector<Data> single_R;
	vector<int> IDs;
	for (int it = 0; it < all_data.size(); it++) {
		IDs.clear();
		IDs = missing_IDs(p_setting.object_max_size, p_setting.R_ratio);
		single_R.clear();
		for (int it2 = 0; it2 < IDs.size(); it2++) {
			int ID_temp = IDs.at(it2);
			Data obj;
			obj.ID = it2;
			obj.actual_ID = all_data.at(it).at(ID_temp).actual_ID;
			obj.attributes = all_data.at(it).at(ID_temp).attributes;
			single_R.push_back(obj);
		}
		data_repository.push_back(single_R);
	}

	return data_repository;
}

void fill_via_ground_truth(vector<vector<Data>>& data, vector<Matching_Record> records, Parameter_Setting& p_setting) {
	for (int it = 0; it < data.size(); it++) {
		int iDS_n = it + 1;
		for (int it2 = 0; it2 < data.at(it).size(); it2++) {
			Data single_object = data.at(it).at(it2);
			string actual_ID = single_object.actual_ID;
			for (int dim1 = 1; dim1 <= p_setting.dimension; dim1++) {
				if (single_object.attributes.at(dim1 - 1).empty()) {
					string matched_actual_ID = "";
					int matched_iDS = -1;
					int matched_ID = -1;
					for (int it3 = 0; it3 < records.size(); it3++) {
						int iDS_n1 = records.at(it3).iDS_n.at(0);
						int iDS_n2 = records.at(it3).iDS_n.at(1);
						string actual_ID1 = records.at(it3).actual_ID.at(0);
						string actual_ID2 = records.at(it3).actual_ID.at(1);
						if (iDS_n == iDS_n1 && actual_ID == actual_ID1) {
							matched_actual_ID = actual_ID2;
							matched_iDS = iDS_n2;
							break;
						}
						else if (iDS_n == iDS_n2 && actual_ID == actual_ID2) {
							matched_actual_ID = actual_ID1;
							matched_iDS = iDS_n1;
							break;
						}
					}

					if (matched_iDS != -1) {
						for (int it3 = 0; it3 < data.at(matched_iDS - 1).size(); it3++) {
							if (matched_actual_ID == data.at(matched_iDS - 1).at(it3).actual_ID) {
								matched_ID = it3;
								break;
							}
						}
					}
					
					if (matched_ID != -1) {
						if (!data.at(matched_iDS - 1).at(matched_ID).attributes.at(dim1 - 1).empty()) {
							data.at(it).at(it2).attributes.at(dim1 - 1) = data.at(matched_iDS - 1).at(matched_ID).attributes.at(dim1 - 1);
						}
						else {
							data.at(it).at(it2).attributes.at(dim1 - 1) = "null";
							data.at(matched_iDS - 1).at(matched_ID).attributes.at(dim1 - 1) = "null";
						}
					}
				}
			}
		}
	}
}

bool check_existance(vector<int> source, int element) {
	bool is_exist = false;
	for (int it = 0; it < source.size(); it++) {
		if (source.at(it) == element) {
			is_exist = true;
			break;
		}
	}
	return is_exist;
}

bool check_existance(vector<string> source, string element) {
	bool is_exist = false;
	for (int it = 0; it < source.size(); it++) {
		if (source.at(it) == element) {
			is_exist = true;
			break;
		}
	}
	return is_exist;
}

vector<vector<Imputed_Data>> imputed_Data_Initialization(vector<vector<Data>> datas, Parameter_Setting p_setting) {
	vector<vector<Imputed_Data>> data_streams;
	vector<Imputed_Data> single_data_stream;
	vector<string> attribute_vals;
	vector<int> val_frequency;
	vector<int> token_size_interval;
	vector<double> dist_interval;

	vector<vector<int>> matched_entities;

	for (int it = 0; it < datas.size(); it++) {
		vector<int> single_file_IDs;
		matched_entities.push_back(single_file_IDs);
	}

	for (int it = 0; it < datas.size(); it++) {
		cout << "file " << it + 1 << ", with size " << datas.at(it).size() << "--------------------" <<  endl;
		single_data_stream.clear();
		vector<int> miss_IDs = missing_IDs(datas.at(it).size(), p_setting.xi);
		for (int it2 = 0; it2 < datas.at(it).size(); it2++) {
			Data object = datas.at(it).at(it2);
			Imputed_Data imputed_object;
			imputed_object.ID = object.ID;
			imputed_object.actual_ID = object.actual_ID;
			imputed_object.iDS_n = it + 1; // data stream IDs start from 1
			cout << "ID = " << imputed_object.ID << "<------------------> actual ID = " << imputed_object.actual_ID << endl;

			for (int it3 = 0; it3 < matched_entities.size(); it3++) {
				imputed_object.matched_entities.push_back(matched_entities.at(it3));
			}

			bool is_exist = check_existance(miss_IDs, imputed_object.ID);

			cout << "missing object?  " << is_exist << endl;

			if (is_exist) {// this object is incomplete
				imputed_object.is_incomplete = true;
				for (int it3 = 0; it3 < p_setting.dimension; it3++) {
					attribute_vals.clear();
					val_frequency.clear();
					token_size_interval.clear();
					dist_interval.clear();
					if (check_existance(p_setting.missing_attributes, it3 + 1)) {
						imputed_object.possible_values.push_back(attribute_vals);
						imputed_object.value_frequency.push_back(val_frequency);
						imputed_object.tokenSizeItv.push_back(token_size_interval);
						imputed_object.distItv.push_back(dist_interval);
						//imputed_object.lb_expectations.push_back(10000);// this value will be re-written in function "data_imputation"
						//imputed_object.ub_expectations.push_back(-1);// this value will be re-written in function "data_imputation"
						imputed_object.expectations.push_back(-1); // we use -1 to represent uncertainty of expection on current dimension
					}
					else {
						attribute_vals.push_back(object.attributes.at(it3));
						imputed_object.possible_values.push_back(attribute_vals);
						val_frequency.push_back(1);
						imputed_object.value_frequency.push_back(val_frequency);

						int token_S = token_size(object.attributes.at(it3));
						token_size_interval.push_back(token_S);
						token_size_interval.push_back(token_S);
						imputed_object.tokenSizeItv.push_back(token_size_interval);

						double dist_temp;
						if (p_setting.is_digits.at(it3)) 
							dist_temp = stod(object.attributes.at(it3));
						else
							dist_temp = Jaccard_Distance(object.attributes.at(it3), p_setting.attribute_pivots.at(it).at(it3).att_pivs.at(0));
						dist_interval.push_back(dist_temp);
						dist_interval.push_back(dist_temp);
						imputed_object.distItv.push_back(dist_interval);

						//imputed_object.lb_expectations.push_back(dist_interval);
						//imputed_object.ub_expectations.push_back(dist_interval);

						imputed_object.expectations.push_back(dist_temp);// expectation is fixed, since only one value on this attribute
					}
				}
			}
			else {
				Instance single_instance;
				for (int it3 = 0; it3 < p_setting.dimension; it3++) {
					attribute_vals.clear();
					val_frequency.clear();
					token_size_interval.clear();
					dist_interval.clear();

					if (!imputed_object.key_exist) {
						istringstream iss;
						iss.str(object.attributes.at(it3));
						string token_tmp;

						do {
							iss >> token_tmp;
							if (!iss.fail()) {
								if (check_existance(p_setting.keywords, token_tmp)) {
									imputed_object.key_exist = true;
									break;
								}
							}
						} while (!iss.fail());

					}

					attribute_vals.push_back(object.attributes.at(it3));
					imputed_object.possible_values.push_back(attribute_vals);
					val_frequency.push_back(1);
					imputed_object.value_frequency.push_back(val_frequency);

					int token_S = token_size(object.attributes.at(it3));
					token_size_interval.push_back(token_S);
					token_size_interval.push_back(token_S);
					imputed_object.tokenSizeItv.push_back(token_size_interval);

					double dist_temp;
					if (p_setting.is_digits.at(it3))
						dist_temp = stod(object.attributes.at(it3));
					else
						dist_temp = Jaccard_Distance(object.attributes.at(it3), p_setting.attribute_pivots.at(it).at(it3).att_pivs.at(0));

					dist_interval.push_back(dist_temp);
					dist_interval.push_back(dist_temp);
					imputed_object.distItv.push_back(dist_interval);

					//imputed_object.lb_expectations.push_back(dist_temp);
					//imputed_object.ub_expectations.push_back(dist_temp);

					imputed_object.expectations.push_back(dist_temp);// expectation is fixed, since only one value on this attribute

					single_instance.attributes.push_back(object.attributes.at(it3));
				}
				single_instance.frequency = 1;
				imputed_object.obj_instances.push_back(single_instance);
			}

			single_data_stream.push_back(imputed_object);
		}
		data_streams.push_back(single_data_stream);
	}

	return data_streams;
}

void norm_numeric(vector<vector<Data>>& objects, Parameter_Setting p_setting) {// this function must be revoked before dectecting CDD rules; this function is to normalize the numeric data.
	double min, max, val_temp;
	for (int it = 0; it < objects.size(); it++) {
		for (int d = 1; d <= p_setting.dimension; d++) {
			if (p_setting.is_digits.at(d - 1)) {// normalize numeric data based on min and max values; only normalize numeric data
				min = INT_MAX;
				max = -1;

				for (int id = 0; id < objects.at(it).size(); id++) {
					//if (it == 1 && id == 458) {
					//	cout << objects.at(it).at(id).actual_ID << endl;
					//	cout << objects.at(it).at(id).attributes.at(0) << endl << endl << endl << endl;
					//	cout << objects.at(it).at(id).attributes.at(1) << endl << endl << endl << endl;
					//	cout << objects.at(it).at(id).attributes.at(2) << endl << endl << endl << endl;
					//	cout << objects.at(it).at(id).attributes.at(3) << endl << endl << endl << endl;
					//}
					val_temp = stod(objects.at(it).at(id).attributes.at(d - 1));
					if (val_temp > max) {
						max = val_temp;
					}
					if (val_temp < min) {
						min = val_temp;
					}
				}

				for (int id = 0; id < objects.at(it).size(); id++) {
					val_temp = stod(objects.at(it).at(id).attributes.at(d - 1));
					val_temp = (val_temp - min) / (max - min);// normalize values into [0, 1]
					objects.at(it).at(id).attributes.at(d - 1) = to_string(val_temp);
				}
			}
		}
	}
}

vector<vector<vector<string>>> attribte_domain(vector<vector<Data>> objects, Parameter_Setting p_setting) {//obtain attribute domains for all files
	vector<vector<vector<string>>> attribute_domains;
	string att_temp;
	for (int it = 0; it < objects.size(); it++) {
		vector<vector<string>> single_file_attribute_domain;
		for (int it2 = 0; it2 < p_setting.dimension; it2++) {
			vector<string> single_attribute_domain;
			for (int it3 = 0; it3 < objects.at(it).size(); it3++) {
				att_temp = objects.at(it).at(it3).attributes.at(it2);
				if (!att_temp.empty() && std::find(single_attribute_domain.begin(), single_attribute_domain.end(), att_temp) == single_attribute_domain.end()) {
					single_attribute_domain.push_back(att_temp);
				}
			}
			single_file_attribute_domain.push_back(single_attribute_domain);
		}
		attribute_domains.push_back(single_file_attribute_domain);
	}

	return attribute_domains;
}

vector<vector<CDD_Rules>> obtain_CDDs(vector<vector<Data>> objects, vector<vector<vector<string>>> v_domains, Parameter_Setting& p_setting) {
	vector<vector<CDD_Rules>> CDDs;
	vector<CDD_Rules> single_file_CDDs;
	CDD_Rules single_CDD;
	vector<vector<vector<int>>> determinant_attributes; //for each vector<int>, it contains two element, the first is for smallest interval; the second is for second smallest interval
	//vector<vector<vector<double>>> Aj_intervals; // dependent attribute intervals
	//double Ax_interval = 1 - p_setting.gamma / p_setting.dimension;// we use the same determinant interval for all CDD rules
	double Ax_interval = p_setting.Ax_interval;
	vector<int> matched_IDs;

	for (int it = 0; it < objects.size(); it++) {
		fstream in(p_setting.CDD_paths.at(it), ios_base::in);
		bool is_CDD_existed;

		if (!in)
		{
			//fail
			in.close();
			is_CDD_existed = false;
		}
		else
		{
			is_CDD_existed = true;
			in.close();
		}

		if (!is_CDD_existed) {
			//-----------------------for each data file, obtain determinant attributes for each dependent attribute start ----------------------
			cout << "----------------------- file " << it + 1 << " obtain determinant attributes for each dependent attribute starts ----------------------" << endl;
			//cout << "file " << it + 1 << "  starts " << endl;
			vector<vector<int>> single_file_determinant_attribute;
			for (int dim1 = 1; dim1 <= p_setting.dimension; dim1++) {
				cout << "dimension " << dim1 << "  starts " << endl;
				vector<int> single_determinant_attribute;
				double smallet_interval = 1, second_smallest_interval = 1, interval_temp;
				single_determinant_attribute.push_back(0);
				single_determinant_attribute.push_back(0);

				for (int dim2 = 1; dim2 <= p_setting.dimension; dim2++) {
					if (dim2 != dim1) {
						interval_temp = obtain_Aj_interval(objects, it + 1, dim2, dim1, p_setting);
						if (interval_temp <= smallet_interval) {
							second_smallest_interval = smallet_interval;
							smallet_interval = interval_temp;
							single_determinant_attribute.at(1) = single_determinant_attribute.at(0);
							single_determinant_attribute.at(0) = dim2;
						}
						else if (interval_temp <= second_smallest_interval) {
							second_smallest_interval = interval_temp;
							single_determinant_attribute.at(1) = dim2;
						}
					}
				}
				single_file_determinant_attribute.push_back(single_determinant_attribute);
				cout << "dimension " << dim1 << "  ends " << endl;
			}
			determinant_attributes.push_back(single_file_determinant_attribute);
			//cout << "file " << it + 1 << "  ends " << endl;
			cout << "-----------------------file " << it + 1 << " obtain determinant attributes for each dependent attribute ends ----------------------" << endl;
			//-----------------------for each data file, obtain determinant attributes for each dependent attribute end ----------------------

			//-----------------------for each data file, generate CDD rules start ----------------------
			cout << "-----------------------obtain CDDs for file " << it + 1 << " starts" << endl;
			single_file_CDDs.clear();
			for (int dim = 1; dim <= p_setting.dimension; dim++) {// dim --> dependent attribute
				single_CDD.Aj_attribute = dim;
				single_CDD.interval_attribute = determinant_attributes.at(it).at(dim - 1).at(0);
				single_CDD.value_attribute = determinant_attributes.at(it).at(dim - 1).at(1);
				single_CDD.Ax_interval = Ax_interval;
				single_CDD.Ax_values.clear();
				single_CDD.Aj_interval.clear();
				cout << "-----------------------obtain CDDs for dimension " << dim << " starts" << endl;

				int value_attribute = single_CDD.value_attribute; // determinant attribute with specific values as constraints
				for (int it2 = 0; it2 < v_domains.at(it).at(value_attribute - 1).size(); it2++) {
					cout << "it2 = " << it2 << endl;
					string constraint_value_temp = v_domains.at(it).at(value_attribute - 1).at(it2);
					single_CDD.Ax_values.push_back(constraint_value_temp);
					matched_IDs.clear();
					for (int it3 = 0; it3 < objects.at(it).size(); it3++) {
						if (objects.at(it).at(it3).attributes.at(value_attribute - 1) == constraint_value_temp) {
							matched_IDs.push_back(objects.at(it).at(it3).ID);
						}
					}
					double Aj_interval_temp = 0;
					double Ax_distance_val, Aj_distance_val;
					for (int it3 = 0; it3 < matched_IDs.size(); it3++) {
						int ID_temp1 = matched_IDs.at(it3);
						for (int it4 = it3 + 1; it4 < matched_IDs.size(); it4++) {
							int ID_temp2 = matched_IDs.at(it4);
							if (p_setting.is_digits.at(value_attribute - 1)) {
								Ax_distance_val = abs(stod(objects.at(it).at(ID_temp1).attributes.at(value_attribute - 1)) - stod(objects.at(it).at(ID_temp2).attributes.at(value_attribute - 1)));
							}
							else {
								Ax_distance_val = Jaccard_Distance(objects.at(it).at(ID_temp1).attributes.at(value_attribute - 1), objects.at(it).at(ID_temp2).attributes.at(value_attribute - 1));
							}

							if (Ax_distance_val <= Ax_interval) {
								if (p_setting.is_digits.at(dim - 1)) {
									Aj_distance_val = abs(stod(objects.at(it).at(ID_temp1).attributes.at(dim - 1)) - stod(objects.at(it).at(ID_temp2).attributes.at(dim - 1)));
								}
								else {
									Aj_distance_val = Jaccard_Distance(objects.at(it).at(ID_temp1).attributes.at(dim - 1), objects.at(it).at(ID_temp2).attributes.at(dim - 1));
								}
								if (Aj_distance_val > Aj_interval_temp) {
									Aj_interval_temp = Aj_distance_val;
								}
							}
						}
					}
					single_CDD.Aj_interval.push_back(Aj_interval_temp);
				}
				single_file_CDDs.push_back(single_CDD);

				cout << "-----------------------obtain CDDs for dimension " << dim << " ends" << endl;
			}
			CDDs.push_back(single_file_CDDs);
			cout << "-----------------------obtain CDDs for file " << it + 1 << " ends" << endl;
			//-----------------------for each data file, generate CDD rules end ----------------------
			//-----------------------for each data file, write CDD rules to local files start ----------------------
			cout << "-----------------------write CDDs for file " << it + 1 << " starts" << endl;
			ofstream fout(p_setting.CDD_paths.at(it));
			int att_temp, cnt_temp;

			for (int dim = 1; dim <= p_setting.dimension; dim++) {
				fout << "CDDs with new dependent attributes" << endl;
				//att_temp = CDDs.at(it).at(dim - 1).value_attribute;
				cnt_temp = CDDs.at(it).at(dim - 1).Ax_values.size();
				fout << CDDs.at(it).at(dim - 1).interval_attribute << "," << CDDs.at(it).at(dim - 1).value_attribute << "," << dim << "," << cnt_temp << endl;
				for (int it2 = 0; it2 < cnt_temp; it2++) {
					fout << Ax_interval << "," << CDDs.at(it).at(dim - 1).Ax_values.at(it2) << "," << CDDs.at(it).at(dim - 1).Aj_interval.at(it2) << endl;
				}
			}

			fout.close();
			cout << "-----------------------write CDDs for file " << it + 1 << " ends" << endl;
			//-----------------------for each data file, write CDD rules to local files end ----------------------
		}
		else {// for each file, read CDDs from local files, since CDDs have been generated before
			cout << "file " << it + 1 << ", CDD rules exit, load from local files starts -----------------------------" << endl;
			single_file_CDDs.clear();
			for (int dim = 1; dim <= p_setting.dimension; dim++) {
				single_CDD.Aj_attribute = dim;
				single_file_CDDs.push_back(single_CDD);
			}
			CDDs.push_back(single_file_CDDs);

			string cddHint = "CDDs with new dependent attributes";
			//single_file_CDDs.clear();

			ifstream in(p_setting.CDD_paths.at(it));
			string line, sub_temp, empty_string = "";

			int smallest_att, second_smallest_att, dependent_att;
			int CDD_cnt, cnt_temp;

			bool Ax_interval_initialized = false;
			//vector<double> Aj_interval_temp;

			double itv_temp;

			istringstream iss;

			if (in)
			{
				getline(in, line);
				while (line == cddHint) {
					getline(in, line);
					iss.clear();
					iss.str(line);

					getline(iss, sub_temp, ',');
					smallest_att = stoi(sub_temp);
					getline(iss, sub_temp, ',');
					second_smallest_att = stoi(sub_temp);
					getline(iss, sub_temp, ',');
					dependent_att = stoi(sub_temp);
					getline(iss, sub_temp, ',');
					CDD_cnt = stoi(sub_temp);

					CDDs.at(it).at(dependent_att - 1).interval_attribute = smallest_att;
					CDDs.at(it).at(dependent_att - 1).value_attribute = second_smallest_att;

					cnt_temp = 0;
					//Aj_interval_temp.clear();

					while (getline(in, line) && cnt_temp < CDD_cnt) {
						iss.clear();
						iss.str(line);
						getline(iss, sub_temp, ',');
						if (!Ax_interval_initialized) {
							Ax_interval = stod(sub_temp);
							Ax_interval_initialized = true;
						}
						CDDs.at(it).at(dependent_att - 1).Ax_interval = Ax_interval;
						getline(iss, sub_temp, ',');
						CDDs.at(it).at(dependent_att - 1).Ax_values.push_back(sub_temp);
						getline(iss, sub_temp, ',');
						itv_temp = stod(sub_temp);
						CDDs.at(it).at(dependent_att - 1).Aj_interval.push_back(itv_temp);

						++cnt_temp;
					}
				}
			}

			in.close();
			cout << "file " << it + 1 << ", CDD rules exit, load from local files ends -----------------------------" << endl;
		}

	}

	return CDDs;
}

void obtain_attribute_pivots(vector<vector<Data>> objects, vector<vector<vector<string>>>& v_domains, Parameter_Setting& p_setting) {

	for (int it = 0; it < objects.size(); it++) {
		fstream in(p_setting.pivot_paths.at(it), ios_base::in);
		bool is_pivots_existed;

		if (!in)
		{
			//fail
			in.close();
			is_pivots_existed = false;
		}
		else
		{
			is_pivots_existed = true;
			in.close();
		}

		if (!is_pivots_existed) {
			/*for each data file, following codes for selecting attribute pivots -----------start */
			cout << "file " << it + 1 << "  , pivot searching starts--------------------" << endl;
			vector<Attribute_Pivots> single_file_att_pivots;
			double curEntropy, attEntropy;// 0 < xlogx < 0.2, for 0 < x < 1 
			string curPiv, val_temp;
			vector<string> current_domain;
			Attribute_Pivots attribute_pivs;
			const int pdf_size = pow(p_setting.parSize, p_setting.pvtCntMax);
			double* pdf = new double[pdf_size];
			int pdf_pos;
			double cur_interval, interval = 1.0 / p_setting.parSize;
			double far_dist, dist_sum;

			for (int d = 1; d <= p_setting.dimension; d++) {
				cout << "attribute " << d << "  starts--------------------" << endl;
				attribute_pivs.attribute = d;
				attribute_pivs.att_pivs.clear();
				if (!p_setting.is_digits.at(d - 1)) {// only textual attributes need pivots
					current_domain.clear();
					current_domain = v_domains.at(it).at(d - 1);

					attEntropy = 0;

					for (int pos = 0; pos < current_domain.size(); pos++) {
						//cout << current_domain.at(pos);
						cout << "debug pos = " << pos << endl;
						if (!current_domain.at(pos).empty()) {
							curPiv = current_domain.at(pos);

							for (int p = 0; p < pdf_size; p++) {
								pdf[p] = 0;
							}

							for (int num = 0; num < objects.at(it).size(); num++) {
								//cout << "file " << it + 1 << "------attribute " << d << "---------debug pos = " << pos << "------------- num = " << num << endl;
								val_temp = objects.at(it).at(num).attributes.at(d - 1);
								cur_interval = interval;
								for (int p = 0; p < p_setting.parSize; p++) {
									if (Jaccard_Distance(curPiv, val_temp) <= cur_interval) {
										pdf[p] = pdf[p] + 1;
										break;
									}
									else {
										cur_interval = cur_interval + interval;
									}
								}
							}

							curEntropy = 0;
							for (int p = 0; p < p_setting.parSize; p++) {
								if (pdf[p] > 0) {
									pdf[p] = pdf[p] / objects.size();
									curEntropy += -1 * pdf[p] * log2(pdf[p]);
								}

							}

							if (attribute_pivs.att_pivs.size() == 0) {
								attEntropy = curEntropy;
								attribute_pivs.att_pivs.push_back(curPiv);
							}
							else if (curEntropy > attEntropy) {
								attEntropy = curEntropy;
								attribute_pivs.att_pivs.at(0) = curPiv;
							}
						}

					}

					//check if more pivots are needed for the d-th attribute
					if (attEntropy < p_setting.entropyMin) {
						while (attEntropy < p_setting.entropyMin && attribute_pivs.att_pivs.size() < p_setting.pvtCntMax) {
							far_dist = 0;
							for (int pos = 0; pos < current_domain.size(); pos++) {
								val_temp = current_domain.at(pos);
								if (!val_temp.empty()) {
									dist_sum = 0;
									for (int pivCnt = 0; pivCnt < attribute_pivs.att_pivs.size(); pivCnt++) {
										dist_sum += Jaccard_Distance(val_temp, attribute_pivs.att_pivs.at(pivCnt));
									}
									if (far_dist < dist_sum) {
										far_dist = dist_sum;
										curPiv = val_temp;
									}
								}

							}
							attribute_pivs.att_pivs.push_back(curPiv);

							for (int p = 0; p < pdf_size; p++) {
								pdf[p] = 0;
							}

							for (int num = 0; num < objects.at(it).size(); num++) {
								val_temp = objects.at(it).at(num).attributes.at(d - 1);
								pdf_pos = 0;
								for (int pivCnt = 1; pivCnt <= attribute_pivs.att_pivs.size(); pivCnt++) {
									cur_interval = interval;
									curPiv = attribute_pivs.att_pivs.at(pivCnt - 1);
									for (int p = 0; p < p_setting.parSize; p++) {
										if (Jaccard_Distance(curPiv, val_temp) <= cur_interval) {
											pdf_pos = pdf_pos + p * pow(p_setting.parSize, attribute_pivs.att_pivs.size() - pivCnt);
											break;
										}
										else {
											cur_interval = cur_interval + interval;
										}
									}
								}

								pdf[pdf_pos] = pdf[pdf_pos] + 1;
							}

							curEntropy = 0;
							for (int p = 0; p < pow(p_setting.parSize, attribute_pivs.att_pivs.size()); p++) {
								if (pdf[p] > 0) {
									pdf[p] = pdf[p] / objects.size();
									curEntropy += -1 * pdf[p] * log2(pdf[p]);
								}

							}

							attEntropy = curEntropy;
						}
					}

				}
				else {
					attribute_pivs.att_pivs.push_back("no need");
				}

				single_file_att_pivots.push_back(attribute_pivs);
				cout << "attribute " << d << "  ends--------------------" << endl;
			}

			delete[] pdf;
			pdf = NULL;
			p_setting.attribute_pivots.push_back(single_file_att_pivots);

			cout << "file " << it + 1 << "  , pivot searching ends--------------------" << endl;
			/*above codes for selecting attribute pivots -----------end */

			/*following codes for writing attribute pivots to local file -----------start */
			cout << "file " << it + 1 << ", writing attribute pivots to local file -----------start" << endl;

			ofstream fout(p_setting.pivot_paths.at(it));
			int att_temp, cnt_temp;

			for (int d = 1; d <= p_setting.dimension; d++) {
				for (int num = 0; num < p_setting.attribute_pivots.at(it).at(d - 1).att_pivs.size(); num++) {
					if (num == p_setting.attribute_pivots.at(it).at(d - 1).att_pivs.size() - 1) {
						fout << p_setting.attribute_pivots.at(it).at(d - 1).att_pivs.at(num);
					}
					else {
						fout << p_setting.attribute_pivots.at(it).at(d - 1).att_pivs.at(num) << ",";
					}
				}
				fout << endl;
			}

			fout.close();
			/*above codes for writing attribute pivots to local file -----------end */
			cout << "file " << it + 1 <<", writing attribute pivots to local file -----------end" << endl;
		}
		else {// local pivots from local files
		/*following codes for reading attribute pivots from local file -----------start */
			cout << "file " << it + 1 << ", pivots exited, reading attribute pivots from local file -----------start" << endl;
			vector<Attribute_Pivots> single_file_att_pivots;
			Attribute_Pivots att_pivots;

			ifstream in(p_setting.pivot_paths.at(it));
			string line, pivot;
			istringstream iss;

			if (in)
			{
				int dimension = 1;
				while (getline(in, line))
				{
					iss.clear();
					iss.str(line);
					att_pivots.att_pivs.clear();
					att_pivots.attribute = dimension;

					while (getline(iss, pivot, ',')) {
						att_pivots.att_pivs.push_back(pivot);
					}
					single_file_att_pivots.push_back(att_pivots);
					dimension++;
				}
				p_setting.attribute_pivots.push_back(single_file_att_pivots);
			}
			else
			{
				std::cout << "no such file" << endl;
			}
			in.close();
			cout << "file " << it + 1 << ", pivots exited, reading attribute pivots from local file -----------end" << endl;
			/*above codes for reading attribute pivots from local file -----------end */
		}

	}


}

vector<vector<vector<CDD_Node>>> establish_CDD_nodes(vector<vector<CDD_Rules>> CDDs, Parameter_Setting& p_setting) {//establish index over all CDD nodes
	//double Ax_interval = 1 - p_setting.gamma / p_setting.dimension;// a determined interval based on dimension and gamma (a special case)
	double Ax_interval = p_setting.Ax_interval;
	vector<vector<vector<CDD_Node>>> CDD_nodes;
	vector<vector<CDD_Node>> single_file_nodes;
	vector<CDD_Node> single_attribute_nodes;
	CDD_Node single_node;
	double distance_temp;
	int value_attribute; //constraint attribute as specific values

	for (int it = 0; it < CDDs.size(); it++) {//CDD_nodes initialization
		single_file_nodes.clear();
		for (int dim = 1; dim <= p_setting.dimension; dim++) {
			single_attribute_nodes.clear();
			for (int it2 = 0; it2 < p_setting.CDDNodeSize; it2++) {
				single_node.cv.clear();
				single_node.CDDID.clear();
				single_node.ID = it2;
				single_node.determinant_attribute = dim;
				single_node.ci = 0;
				single_node.di = 0;
				for (int it3 = 0; it3 < p_setting.pvtCntMax; it3++) {
					single_node.cv.push_back(1);
					single_node.cv.push_back(0);
				}
				single_attribute_nodes.push_back(single_node);
			}
			single_file_nodes.push_back(single_attribute_nodes);
		}
		CDD_nodes.push_back(single_file_nodes);
	}

	for (int it = 0; it < CDDs.size(); it++) {
		for (int dim = 1; dim <= p_setting.dimension; dim++) {
			value_attribute = CDDs.at(it).at(dim - 1).value_attribute;
			for (int it2 = 0; it2 < CDDs.at(it).at(dim - 1).Ax_values.size(); it2++) {
				string current_value = CDDs.at(it).at(dim - 1).Ax_values.at(it2);
				//if (current_value == "fun with reading & writing! is designed to help kids learn to read and write better through exercises puzzle-solving creative writing decoding and more!")
				//	cout << "debug here" << endl;
				//if (dim == 4 && it2 == 10)
				//	cout << "debug here" << endl;

				if (p_setting.is_digits.at(value_attribute - 1)) {
					distance_temp = stod(current_value);
				}
				else {
					distance_temp = Jaccard_Distance(p_setting.attribute_pivots.at(it).at(value_attribute - 1).att_pivs.at(0), current_value);
					//distance_temp = Jaccard_Distance(p_setting.attribute_pivots.at(it).at(dim - 1).att_pivs.at(0), current_value);
				}
				int nodePos = (int)(distance_temp * p_setting.CDDNodeSize);// the position of the CDD nodes in the index that contain the specific values "current_value"; based on the main pivot
				if (nodePos >= p_setting.CDDNodeSize) {// the maximal number of CDD nodes is CDDNodeSize - 1, since it starts from 0
					nodePos = p_setting.CDDNodeSize - 1;
				}
				CDD_nodes.at(it).at(dim - 1).at(nodePos).CDDID.push_back(it2);// put the position of CDD with specific value "current_value" into the node in index at position nodePos
				CDD_nodes.at(it).at(dim - 1).at(nodePos).ci = Ax_interval;// we set the intervals of determinant attributes as the same (i.e., Ax_interval) in this implementation
				if (CDDs.at(it).at(dim - 1).Aj_interval.at(it2) > CDD_nodes.at(it).at(dim - 1).at(nodePos).di) {// update the interval of dependent attributes in this index node
					CDD_nodes.at(it).at(dim - 1).at(nodePos).di = CDDs.at(it).at(dim - 1).Aj_interval.at(it2);
				}
				if (p_setting.is_digits.at(value_attribute - 1)) {// for numeric data
					for (int pvtNum = 0; pvtNum < p_setting.pvtCntMax; pvtNum++) {
						if (pvtNum == 0) {
							if (distance_temp < CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum)) {
								CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum) = distance_temp;
							}
							if (distance_temp > CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1)) {
								CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1) = distance_temp;
							}
						}
						else {// numeric data doesn't need attribute pivots
							CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum) = -1;
							CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1) = -1;
						}
					}

				}
				else {//update the intervals of distances between specific values and attribute pivots
					for (int pvtNum = 0; pvtNum < p_setting.pvtCntMax; pvtNum++) {
						if (pvtNum == 0) {// distances w.r.t. the main pivot is calculated above
							if (distance_temp < CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum)) {
								CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum) = distance_temp;
							}
							if (distance_temp > CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1)) {
								CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1) = distance_temp;
							}
						}
						else {
							if (pvtNum < p_setting.attribute_pivots.at(it).at(value_attribute - 1).att_pivs.size()) {// the actual pivot number may be smaller than the pvtCntMax
								distance_temp = Jaccard_Distance(p_setting.attribute_pivots.at(it).at(value_attribute - 1).att_pivs.at(pvtNum), current_value);
								if (distance_temp < CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum)) {
									CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum) = distance_temp;
								}
								if (distance_temp > CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1)) {
									CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1) = distance_temp;
								}
							}
							else {
								CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum) = -1;
								CDD_nodes.at(it).at(dim - 1).at(nodePos).cv.at(2 * pvtNum + 1) = -1;
							}

						}
					}
				}

			}
		}
	}

	return CDD_nodes;
}

void write_converted_data(vector<vector<Data>> objects, Parameter_Setting& p_setting) {// the coverted data is for aR-tree
	for (int it = 0; it < objects.size(); it++) {
		fstream in(p_setting.converted_file_paths.at(it), ios_base::in);
		bool is_data_converted;

		if (!in)
		{
			//fail
			in.close();
			is_data_converted = false;
		}
		else
		{
			is_data_converted = true;
			in.close();
		}

		if (!is_data_converted) {
			ofstream fout(p_setting.converted_file_paths.at(it));
			double value_temp;

			for (int it2 = 0; it2 < objects.at(it).size(); it2++) {
				for (int d = 1; d <= p_setting.dimension; d++) {
					if (p_setting.is_digits.at(d - 1)) {
						value_temp = stod(objects.at(it).at(it2).attributes.at(d - 1));
					}
					else {
						value_temp = Jaccard_Distance(p_setting.attribute_pivots.at(it).at(d - 1).att_pivs.at(0), objects.at(it).at(it2).attributes.at(d - 1));// convert data based on main attributes
					}

					if (d == p_setting.dimension) {
						fout << value_temp << " " << value_temp;// value twice, which serves as min and max value, for inserting into R-tree.
					}
					else {
						fout << value_temp << " " << value_temp << " ";
					}

				}
				if (it2 < objects.at(it).size() - 1) {
					fout << endl;
				}
			}

			fout.close();
		}
	}
}

void obtain_aRtree_nodes(Parameter_Setting& p_setting) {// return the R-tree root
	
	for (int it = 0; it < p_setting.tree_file_paths.size(); it++) {
		
		RTree* rt = NULL;
		int base = 1024;

		int data_file_size = p_setting.converted_file_paths.at(it).length();
		char* converted_data_path = new char[data_file_size + 1];
		strcpy(converted_data_path, p_setting.converted_file_paths.at(it).c_str());

		int tree_file_size = p_setting.tree_file_paths.at(it).length();
		char* tree_path = new char[tree_file_size + 1];
		strcpy(tree_path, p_setting.tree_file_paths.at(it).c_str());

		ifstream in(p_setting.tree_file_paths.at(it));
		if (in) {
			remove(tree_path);
		}
	
		rt = new RTree(converted_data_path, tree_path, base * p_setting.dimension, NULL, p_setting.dimension);

		p_setting.tree_roots.push_back(rt);
	}
	

	/*
	for (int it = 0; it < p_setting.stream_paths.size(); it++) {
		RTree* rt = NULL;
		int base = 1024;
		int data_file_size = p_setting.converted_file_paths.at(it).length();
		char* converted_data_path = new char[data_file_size + 1];
		strcpy(converted_data_path, p_setting.converted_file_paths.at(it).c_str());

		int tree_file_size = p_setting.tree_file_paths.at(it).length();
		char* tree_path = new char[tree_file_size + 1];
		strcpy(tree_path, p_setting.tree_file_paths.at(it).c_str());

		rt = new RTree(converted_data_path, tree_path, base * p_setting.dimension, NULL, p_setting.dimension);
		p_setting.tree_roots.push_back(rt);
	}
	*/
}

void obtain_all_node_IDs(RTree* tree_root, int node_ID, vector<int>& IDs) {// obtain the IDs of all data nodes under the node with ID "node_ID" (not data points)
	RTNode* node = new RTNode(tree_root, node_ID);
	//IDs.push_back(node_ID);

	if (!node->is_data_node()) {// only for all nodes (at least data nodes), not data points
		for (int i = 0; i < node->num_entries; i++) {
			obtain_all_node_IDs(tree_root, node->entries[i].son, IDs);
		}
	}
	else {
		IDs.push_back(node_ID);
	}
}

void obtain_all_data_IDs(RTree* tree_root, int node_ID, vector<int>& data_IDs) {// obtain IDs of all data points under current node (with ID node_ID)
	RTNode* node = new RTNode(tree_root, node_ID);

	if (node->is_data_node()) {
		for (int i = 0; i < node->num_entries; i++) {
			data_IDs.push_back(node->entries[i].son);
		}
	}
	else {
		for (int i = 0; i < node->num_entries; i++) {
			obtain_all_data_IDs(tree_root, node->entries[i].son, data_IDs);
		}
	}
}

int which_node(RTree* tree_root, int data_ID) {// return which RTtree node contains a specific data
	int which_node = -1;
	bool is_found = false;

	vector<int> IDs;
	obtain_all_node_IDs(tree_root, tree_root->root, IDs);

	for (int it = 0; it < IDs.size(); it++) {
		vector<int> data_IDs;
		obtain_all_data_IDs(tree_root, IDs.at(it), data_IDs);
		for (int it2 = 0; it2 < data_IDs.size(); it2++) {
			if (data_IDs.at(it2) == data_ID) {
				which_node = IDs.at(it);
				is_found = true;
				break;
			}
		}
		if (is_found)
			break;
	}

	return which_node;
}

vector<vector<R_Node>> obtain_node_information_for_R(vector<vector<Data>> objects, Parameter_Setting& p_setting) {// return the node information
	vector<vector<R_Node>> all_R_nodes;
	for (int it = 0; it < objects.size(); it++) {
		RTree* tree_root = p_setting.tree_roots.at(it);
		vector<int> node_IDs;
		obtain_all_node_IDs(tree_root, tree_root->root, node_IDs);// obtain all data nodes (not data points)
		std::sort(node_IDs.begin(), node_IDs.end());
		vector<R_Node> single_file_R_nodes;
		vector<int> size_interval;
		vector<double> dist_interval;

		cout << "file " << it + 1 << "-------------------------" << endl;
		cout << "R nodes initialization starts-------------------------" << endl;
		//for (int it2 = 0; it2 <= node_IDs.at(node_IDs.size() - 1); it2++) {// initialize R_nodes; obtain the maximal node ID (integer) in R*-tree 
		for (int it2 = 0; it2 < node_IDs.size(); it2++) {// initialize R_nodes
			struct R_Node newNode;
			newNode.nodeID = node_IDs.at(it2);
			for (int dim = 1; dim <= p_setting.dimension; dim++) {
				size_interval.clear();
				size_interval.push_back(100000);
				size_interval.push_back(-1);

				newNode.tokenSizeItv.push_back(size_interval);

				dist_interval.clear();
				for (int piv_cnt = 0; piv_cnt < p_setting.pvtCntMax; piv_cnt++) {
					dist_interval.push_back(1);
					dist_interval.push_back(0);
				}

				newNode.distItv.push_back(dist_interval);
			}

			single_file_R_nodes.push_back(newNode);
		}
		

		vector<int> data_IDs;
		string val_string;
		int ID_temp;
		bool exist_flag;
		double dist_itv_temp;
		int size_itv_temp;

		for (int it2 = 0; it2 < node_IDs.size(); it2++) {
			int temp_ID = node_IDs.at(it2);
			cout << "RNode ID = " << temp_ID << "------------------------" << endl;
			//single_file_R_nodes.at(temp_ID).nodeID = temp_ID;// the node with nodeID as -1 is empty; in other words, this node does not exist in the R-tree

			data_IDs.clear();
			obtain_all_data_IDs(tree_root, temp_ID, data_IDs);// obtain all data points within this node with ID temp_ID
			std::sort(data_IDs.begin(), data_IDs.end());// this is not required, for the debug purpose
			//if (check_existance(data_IDs, 1410))
			//	cout << "debug here" << endl;

			exist_flag = false;

			for (int it3 = 0; it3 < data_IDs.size(); it3++) {
				ID_temp = data_IDs.at(it3) - 1; // data ID in R-tree starts from 1, ID in objs starts from 0;
				for (int dim = 1; dim <= p_setting.dimension; dim++) {
					val_string = objects.at(it).at(ID_temp).attributes.at(dim - 1);
					if (!exist_flag) {
						for (int kcnt = 0; kcnt < p_setting.keywords.size(); kcnt++) {
							if (val_string.find(p_setting.keywords.at(kcnt)) != std::string::npos) {
								exist_flag = true;
								single_file_R_nodes.at(it2).key_exist = true; // set the key_exist in the node as true
								break;
							}
						}
					}

					if (!p_setting.is_digits.at(dim - 1)) {// calculate the distance intervals and size intervals, only for string attributes
						size_itv_temp = token_size(val_string);
						if (size_itv_temp < single_file_R_nodes.at(it2).tokenSizeItv.at(dim - 1).at(0)) {// update the node information related to size intervals
							single_file_R_nodes.at(it2).tokenSizeItv.at(dim - 1).at(0) = size_itv_temp;
						}

						if (size_itv_temp > single_file_R_nodes.at(it2).tokenSizeItv.at(dim - 1).at(1)) {
							single_file_R_nodes.at(it2).tokenSizeItv.at(dim - 1).at(1) = size_itv_temp;
						}

						for (int piv_cnt = 0; piv_cnt < p_setting.attribute_pivots.at(it).at(dim - 1).att_pivs.size(); piv_cnt++) {// update the node information related to distance intervals w.r.t. pivots
							dist_itv_temp = Jaccard_Distance(val_string, p_setting.attribute_pivots.at(it).at(dim - 1).att_pivs.at(piv_cnt));

							if (dist_itv_temp < single_file_R_nodes.at(it2).distItv.at(dim - 1).at(2 * piv_cnt)) {
								single_file_R_nodes.at(it2).distItv.at(dim - 1).at(2 * piv_cnt) = dist_itv_temp;
							}

							if (dist_itv_temp > single_file_R_nodes.at(it2).distItv.at(dim - 1).at(2 * piv_cnt + 1)) {
								single_file_R_nodes.at(it2).distItv.at(dim - 1).at(2 * piv_cnt + 1) = dist_itv_temp;
							}
						}
					}

				}
			}
		}

		all_R_nodes.push_back(single_file_R_nodes);

		cout << "R nodes initialization ends-------------------------" << endl;
	}

	return all_R_nodes;
}

vector<vector<Grid_Cell>> initialize_grid_cell(Parameter_Setting& p_setting) {//index for grid; 
	vector<vector<Grid_Cell>> ER_grids;
	vector<int> size_interval;
	vector<double> dist_interval;

	//double cell_length = dimension - gamma;
	if (p_setting.cell_length > 1) {// this length is at most 1
		p_setting.cell_length = 1.0;
	}

	int piece_cnt = ceil(1 / p_setting.cell_length);// the number of pieces, where each piece has length cell_length (the last piece may have cell length < cell_length)
	int cell_cnt = pow(piece_cnt, p_setting.dimension);

	for (int it = 0; it < p_setting.stream_paths.size(); it++) {
		vector<Grid_Cell> single_file_ER_grid;
		int num_temp, quotient;// these variables are for filling the main_distItv of each cell
		for (int it2 = 0; it2 < cell_cnt; it2++) {
			struct Grid_Cell new_cell;
			new_cell.cell_ID = it2;
			num_temp = it2;
			for (int dim = 1; dim <= p_setting.dimension; dim++) {
				quotient = num_temp / pow(piece_cnt, p_setting.dimension - dim);
				new_cell.main_distItv.push_back(quotient * p_setting.cell_length);
				if (quotient >= piece_cnt - 1) {
					new_cell.main_distItv.push_back(1);
				}
				else {
					new_cell.main_distItv.push_back((quotient + 1) * p_setting.cell_length);
				}

				num_temp = num_temp % (int)pow(piece_cnt, p_setting.dimension - dim);

				size_interval.clear();
				size_interval.push_back(100000);
				size_interval.push_back(-1);

				new_cell.tokenSizeItv.push_back(size_interval);

				dist_interval.clear();
				for (int piv_cnt = 0; piv_cnt < p_setting.pvtCntMax; piv_cnt++) {
					dist_interval.push_back(1);
					dist_interval.push_back(0);
				}

				new_cell.distItv.push_back(dist_interval);
			}

			single_file_ER_grid.push_back(new_cell);
		}
		ER_grids.push_back(single_file_ER_grid);
	}
	return ER_grids;
}

vector<int> cells_intersected(vector<vector<Grid_Cell>> ER_grids, Imputed_Data ip_data, Parameter_Setting& p_setting) {// this function returns the list of cells that intersect with the imputed object; only based on main attribute pivots
	//double cell_length = dimension - gamma;
	if (p_setting.cell_length > 1) {// this length is at most 1
		p_setting.cell_length = 1;
	}

	int piece_cnt = ceil(1 / p_setting.cell_length);// the number of pieces, where each piece has length cell_length (the last piece may have cell length < cell_length)
	int cell_cnt = pow(piece_cnt, p_setting.dimension);

	int iDS_n = ip_data.iDS_n;

	vector<int> cell_IDs_intersected;

	bool is_intersected;
	for (int cnt = 0; cnt < cell_cnt; cnt++) {
		Grid_Cell cell_tmp = ER_grids.at(iDS_n - 1).at(cnt);
		is_intersected = true;
		for (int dim = 1; dim <= p_setting.dimension; dim++) {
			if (cell_tmp.main_distItv.at(2 * (dim - 1)) > ip_data.distItv.at(dim - 1).at(1) || ip_data.distItv.at(dim - 1).at(0) > cell_tmp.main_distItv.at(2 * (dim - 1) + 1)) {
				is_intersected = false;
				break;
			}
		}
		if (is_intersected) {
			cell_IDs_intersected.push_back(cell_tmp.cell_ID);
		}
	}

	return cell_IDs_intersected;
}

void data_imputation(Imputed_Data& object, vector<vector<vector<CDD_Node>>> CDD_index, vector<vector<CDD_Rules>> CDDs, RTree* tree_root, vector<vector<R_Node>>& R_Nodes, vector<vector<Data>>& data_repository, vector<vector<vector<string>>>& v_domains, bool is_fully_imputed, vector<vector<int>>& CDDNode_IDs, vector<vector<int>>& RNode_IDs, Parameter_Setting p_setting) {
	// CDDNode_IDs --> record the possible CDD IDs that may be used for fully imputation
	// RNode_IDs --> record the possible RNode IDs that may be used for fully imputation
	//double Ax_interval = 1 - p_setting.gamma / p_setting.dimension;// a determined interval based on dimension and gamma (a special case)
	double Ax_interval = p_setting.Ax_interval;
	vector<int> CDDNode_IDs_temp;// this is to record IDs for each attribute
	vector<int> RNode_IDs_temp;
	int iDS_n = object.iDS_n;
	if (!is_fully_imputed) {
		for (int it = 0; it < p_setting.missing_attributes.size(); it++) {
			CDDNode_IDs_temp.clear();
			RNode_IDs_temp.clear();

			int missing_attribute = p_setting.missing_attributes.at(it);
			int constraint_attribute_ID = CDDs.at(iDS_n - 1).at(missing_attribute - 1).value_attribute;
			string constraint_value = object.possible_values.at(constraint_attribute_ID - 1).at(0);
			double distance_temp;
			if (p_setting.is_digits.at(constraint_attribute_ID - 1)) {
				distance_temp = stod(constraint_value);
			}
			else {
				distance_temp = Jaccard_Distance(p_setting.attribute_pivots.at(iDS_n - 1).at(constraint_attribute_ID - 1).att_pivs.at(0), constraint_value);
			}

			int nodePos = (int)(distance_temp * p_setting.CDDNodeSize);// the position of the CDD nodes in the index that contain the specific values "constraint_value"; based on the main pivot
			if (nodePos >= p_setting.CDDNodeSize) {// the maximal number of CDD nodes is CDDNodeSize - 1, since it starts from 0
				nodePos = p_setting.CDDNodeSize - 1;
			}
			CDDNode_IDs_temp.push_back(nodePos);// record the CDD node ID, for future fully imputation
			CDDNode_IDs.push_back(CDDNode_IDs_temp);

			//------------search over data repository for blurry imputation-------------------
			int interval_attribute_ID = CDDs.at(iDS_n - 1).at(missing_attribute - 1).interval_attribute;// the determinant attribute ID with interval as constraints
			string interval_attribute = object.possible_values.at(interval_attribute_ID - 1).at(0); // this value is not an interval, but an attribute value on determinant attribute with interval as constraints
			double distance_temp_2;
			if (p_setting.is_digits.at(interval_attribute_ID - 1)) {
				distance_temp_2 = stod(interval_attribute);
			}
			else {
				distance_temp_2 = Jaccard_Distance(p_setting.attribute_pivots.at(iDS_n - 1).at(interval_attribute_ID - 1).att_pivs.at(0), interval_attribute);
			}

			for (int it2 = 0; it2 < R_Nodes.at(iDS_n - 1).size(); it2++) {
				if (R_Nodes.at(iDS_n - 1).at(it2).distItv.at(constraint_attribute_ID - 1).at(0) <= distance_temp &&
					distance_temp <= R_Nodes.at(iDS_n - 1).at(it2).distItv.at(constraint_attribute_ID - 1).at(1)) {// satisfy the requirement of specific values as constraints
					double dist_temp1 = abs(R_Nodes.at(iDS_n - 1).at(it2).distItv.at(interval_attribute_ID - 1).at(0) - distance_temp_2);
					double dist_temp2 = abs(R_Nodes.at(iDS_n - 1).at(it2).distItv.at(interval_attribute_ID - 1).at(1) - distance_temp_2);
					double lower_bound;
					if (dist_temp1 <= dist_temp2)
						lower_bound = dist_temp1;
					else
						lower_bound = dist_temp2;

					if (lower_bound <= Ax_interval) {// satisfy the requirement of interval as constraints
						//RNode_IDs_temp.push_back(R_Nodes.at(iDS_n - 1).at(it2).nodeID);
						RNode_IDs_temp.push_back(it2);
					}

				}

			}

			RNode_IDs.push_back(RNode_IDs_temp);

		}
	}

	if (is_fully_imputed) {// this object needs fully imputation, since the index node level cannot help
						   // strategy: first find all available CDD rules, and then impute object 
		vector<vector<int>> available_CDD_IDs;
		vector<int> available_CDD_IDs_temp;
		for (int it = 0; it < p_setting.missing_attributes.size(); it++) {
			available_CDD_IDs_temp.clear();
			int missing_attribute = p_setting.missing_attributes.at(it);
			for (int it2 = 0; it2 < CDDNode_IDs.at(it).size(); it2++) {// actually, only one ID interests in this vector (i.e., CDDNode_IDs.at(it).size() == 1)
				int current_CDDNode_ID = CDDNode_IDs.at(it).at(it2);
				for (int it3 = 0; it3 < CDD_index.at(iDS_n - 1).at(missing_attribute - 1).at(current_CDDNode_ID).CDDID.size(); it3++) {
					int current_CDD_ID = CDD_index.at(iDS_n - 1).at(missing_attribute - 1).at(current_CDDNode_ID).CDDID.at(it3); // CDD ID can be used 
					//check whether this CDD_ID can be used for imputation
					int value_attribute = CDDs.at(iDS_n - 1).at(missing_attribute - 1).value_attribute;
					int interval_attribute = CDDs.at(iDS_n - 1).at(missing_attribute - 1).interval_attribute;
					string constraint_value = object.possible_values.at(value_attribute - 1).at(0);
					string interval_value = object.possible_values.at(interval_attribute - 1).at(0);
					double distance_temp;
					if (CDDs.at(iDS_n - 1).at(missing_attribute - 1).Ax_values.at(current_CDD_ID) == constraint_value) {// specific values are matched
						for (int it4 = 0; it4 < RNode_IDs.at(it).size(); it4++) {
							int current_RNode_ID = R_Nodes.at(iDS_n - 1).at(RNode_IDs.at(it).at(it4)).nodeID;
							vector<int> potential_data_IDs;
							obtain_all_data_IDs(p_setting.tree_roots.at(iDS_n - 1), current_RNode_ID, potential_data_IDs);
							for (int it5 = 0; it5 < potential_data_IDs.size(); it5++) {
								int current_R_data_ID = potential_data_IDs.at(it5) - 1;// ID in R-tree starts from 1, ID in data repository starts from 0
								//if (current_R_data_ID == 1) {
								//	cout << "debug here" << endl;
								//}
								string R_constraint_value = data_repository.at(iDS_n - 1).at(current_R_data_ID).attributes.at(value_attribute - 1);
								string R_interval_value = data_repository.at(iDS_n - 1).at(current_R_data_ID).attributes.at(interval_attribute - 1);
								if (constraint_value == R_constraint_value) {
									if (p_setting.is_digits.at(interval_attribute - 1)) {
										distance_temp = abs(stod(interval_value) - stod(R_interval_value));
									}
									else {
										distance_temp = Jaccard_Distance(interval_value, R_interval_value);
									}
									if (distance_temp <= CDDs.at(iDS_n - 1).at(missing_attribute - 1).Ax_interval) {// interval constraints are matched
										// current complete data from data repository R can be used for imputing object
										string possible_value_seed = data_repository.at(iDS_n - 1).at(current_R_data_ID).attributes.at(missing_attribute - 1);
										//--> use the seed to find more potential values, if time cost is good
										//for (int it6 = 0; it6 < v_domains.at(iDS_n - 1).at(missing_attribute - 1).size(); it6++) {} 
										bool is_value_exist = false;
										for (int it6 = 0; it6 < object.possible_values.at(missing_attribute - 1).size(); it6++) {
											if (object.possible_values.at(missing_attribute - 1).at(it6) == possible_value_seed) {// increase the count of already founded potential values
												object.value_frequency.at(missing_attribute - 1).at(it6) = object.value_frequency.at(missing_attribute - 1).at(it6) + 1;
												is_value_exist = true;
												break;
											}
											//else {// push_back the new potential values and intialize the counts
											//	object.possible_values.at(missing_attribute - 1).push_back(possible_value_seed);
											//	object.value_frequency.at(missing_attribute - 1).push_back(1);
											//}
										}
										if (!is_value_exist) {
											object.possible_values.at(missing_attribute - 1).push_back(possible_value_seed);
											object.value_frequency.at(missing_attribute - 1).push_back(1);
										}
									}
								}
							}
						}

					}
				}
			}
			if (object.possible_values.at(missing_attribute - 1).size() == 0) {//imputation fails, no suitable values found
				if (p_setting.is_digits.at(missing_attribute - 1)) {
					object.possible_values.at(missing_attribute - 1).push_back(to_string(-1));
				}
				else {
					object.possible_values.at(missing_attribute - 1).push_back("not found");
				}
				object.value_frequency.at(missing_attribute - 1).push_back(1);
			}
		}

		object.imputed_complete = true;

		//following codes will update the flag key_exist and three statistics: distItv, tokenSizeItv, and expectations
		for (int dim = 1; dim <= p_setting.dimension; dim++) {
			double distItv_sum = 0;
			for (int it = 0; it < object.possible_values.at(dim - 1).size(); it++) {
				string current_val = object.possible_values.at(dim - 1).at(it);
				if (!object.key_exist) {// check whether or not this object may contain any keyword
					istringstream iss;
					iss.str(current_val);
					string token_tmp;

					do {
						iss >> token_tmp;
						if (!iss.fail()) {
							if (check_existance(p_setting.keywords, token_tmp)) {
								object.key_exist = true;
								break;
							}
						}
					} while (!iss.fail());

				}
				int current_token_size = token_size(current_val);
				double current_dist_temp;
				if (check_existance(p_setting.missing_attributes, dim)) {// dimension dim is incomplete; object.tokenSizeItv.at(dim - 1).size() == 0
					object.tokenSizeItv.at(dim - 1).push_back(current_token_size);
					object.tokenSizeItv.at(dim - 1).push_back(current_token_size);

					if (p_setting.is_digits.at(dim - 1)) {// for digit value, no need for convertion via pivots
						current_dist_temp = stod(current_val);
						distItv_sum = distItv_sum + current_dist_temp;
						if (object.distItv.at(dim - 1).size() == 0) {// the distItv hasn't been initialized yet
							object.distItv.at(dim - 1).push_back(current_dist_temp);
							object.distItv.at(dim - 1).push_back(current_dist_temp);
						}
					}
					else {
						if (object.distItv.at(dim - 1).size() == 0) {// distItv hasn't been initialized yet, w.r.t. pivots
							for (int it2 = 0; it2 < p_setting.attribute_pivots.at(iDS_n - 1).at(dim - 1).att_pivs.size(); it2++) {
								current_dist_temp = Jaccard_Distance(p_setting.attribute_pivots.at(iDS_n - 1).at(dim - 1).att_pivs.at(it2), current_val);
								object.distItv.at(dim - 1).push_back(current_dist_temp);
								object.distItv.at(dim - 1).push_back(current_dist_temp);
								if (it2 == 0)// only based on main attribute pivot in this implementation
									distItv_sum = distItv_sum + current_dist_temp;
							}
						}
						else {
							for (int it2 = 0; it2 < p_setting.attribute_pivots.at(iDS_n - 1).at(dim - 1).att_pivs.size(); it2++) {
								current_dist_temp = Jaccard_Distance(p_setting.attribute_pivots.at(iDS_n - 1).at(dim - 1).att_pivs.at(it2), current_val);
								if (object.distItv.at(dim - 1).at(2 * it2) > current_dist_temp)
									object.distItv.at(dim - 1).at(2 * it2) = current_dist_temp;
								if (object.distItv.at(dim - 1).at(2 * it2 + 1) < current_dist_temp)
									object.distItv.at(dim - 1).at(2 * it2 + 1) = current_dist_temp;
								if (it2 == 0)// only based on main attribute pivot in this implementation
									distItv_sum = distItv_sum + current_dist_temp;
							}
						}

					}
				}
				else {// for complete attribute, this size interal has been initialized in function imputed_Data_Initialization 
					if (object.tokenSizeItv.at(dim - 1).at(0) > current_token_size)
						object.tokenSizeItv.at(dim - 1).at(0) = current_token_size;
					if (object.tokenSizeItv.at(dim - 1).at(1) < current_token_size)
						object.tokenSizeItv.at(dim - 1).at(1) = current_token_size;
				}
			}
			if (check_existance(p_setting.missing_attributes, dim)) {
				double distItv_average = distItv_sum / object.possible_values.at(dim - 1).size();
				object.expectations.at(dim - 1) = distItv_average;
			}
		}

	}
}

bool Theorems1_4(Imputed_Data object1, Imputed_Data object2, Parameter_Setting p_setting) {// apply pruning Theorems 4.1--4.3
	bool is_pruned = false;

	if (!object1.key_exist && !object2.key_exist) {// Theorem 4.1
		is_pruned = true;
	}

	/*
	double ub_sim = 0;

	if (!is_pruned) {// Theorem 4.2 --> Lemma 4.1
		for (int dim = 1; dim <= p_setting.dimension; dim++) {
			double ub_sim_attribute = 0;
			if (object1.tokenSizeItv.at(dim - 1).at(0) > object2.tokenSizeItv.at(dim - 1).at(1)) {
				ub_sim_attribute = ((double)object2.tokenSizeItv.at(dim - 1).at(1)) / object1.tokenSizeItv.at(dim - 1).at(0);
			}
			else if (object1.tokenSizeItv.at(dim - 1).at(1) < object2.tokenSizeItv.at(dim - 1).at(0)) {
				ub_sim_attribute = ((double)object1.tokenSizeItv.at(dim - 1).at(1)) / object2.tokenSizeItv.at(dim - 1).at(0);
			}
			else {
				ub_sim_attribute = 1;
			}
			ub_sim = ub_sim + ub_sim_attribute;
		}

		if (ub_sim <= p_setting.gamma) {
			is_pruned = true;
		}
	}

	double min_dist = 0;
	if (!is_pruned) {//Theorem 4.2 --> Lemma 4.2
		for (int dim = 1; dim <= p_setting.dimension; dim++) {
			double min_dist_attribute = 0;
			if (object1.distItv.at(dim - 1).at(0) > object2.distItv.at(dim - 1).at(1)) {
				min_dist_attribute = object1.distItv.at(dim - 1).at(0) - object2.distItv.at(dim - 1).at(1);
			}
			else if (object2.distItv.at(dim - 1).at(0) > object1.distItv.at(dim - 1).at(1)) {
				min_dist_attribute = object2.distItv.at(dim - 1).at(0) - object1.distItv.at(dim - 1).at(1);
			}
			else {
				min_dist_attribute = 0;
			}
			min_dist = min_dist + min_dist_attribute;
		}
		ub_sim = p_setting.dimension - min_dist;
		if (ub_sim <= p_setting.gamma) {
			is_pruned = true;
		}
	}

	if (!is_pruned) {// Theorem 4.3
		double UB_prob = 1;
		double E_x = 0, E_y = 0, ub_X = 0, lb_X = 0, ub_Y = 0, lb_Y = 0;
		for (int dim = 1; dim <= p_setting.dimension; dim++) {
			E_x = E_x + object1.expectations.at(dim - 1);
			E_y = E_y + object2.expectations.at(dim - 1);
			lb_X = lb_X + object1.distItv.at(dim - 1).at(0);
			ub_X = ub_X + object1.distItv.at(dim - 1).at(1);
			lb_Y = lb_Y + object2.distItv.at(dim - 1).at(0);
			ub_Y = ub_Y + object2.distItv.at(dim - 1).at(1);
		}

		if (E_x > E_y) {
			double prob_temp1 = (p_setting.dimension - p_setting.gamma) / (E_x - E_y);
			if (0 <= prob_temp1 && prob_temp1 <= 1 && lb_X >= ub_Y) {
				UB_prob = 1 - pow(1 - prob_temp1, 2) * (E_x - E_y) / (ub_X - lb_Y);
			}
		}
		else if (E_y > E_x) {
			double prob_temp2 = (p_setting.dimension - p_setting.gamma) / (E_y - E_x);
			if (0 <= prob_temp2 && prob_temp2 <= 1 && lb_Y >= ub_X) {
				UB_prob = 1 - pow(1 - prob_temp2, 2) * (E_y - E_x) / (ub_Y - lb_X);
			}
		}
		else {
			UB_prob = 1;
		}

		if (UB_prob < p_setting.alpha)
			is_pruned = true;
	}
	*/

	
	if (!is_pruned) {// Theorem 4.4
		vector<Instance> object1_instances = object1.obj_instances;
		vector<Instance> object2_instances = object2.obj_instances;
		int checked_pair_cnt = 0, matched_pair_cnt = 0;
		int ins_freq_cnt1 = 0, ins_freq_cnt2 = 0;
		for (int it = 0; it < object1_instances.size(); it++) {
			ins_freq_cnt1 = ins_freq_cnt1 + object1_instances.at(it).frequency;
		}
		for (int it = 0; it < object2_instances.size(); it++) {
			ins_freq_cnt2 = ins_freq_cnt2 + object2_instances.at(it).frequency;
		}
		double total_pair_cnt = ins_freq_cnt1 * ins_freq_cnt2;
		for (int it = 0; it < object1_instances.size(); it++) {
			Instance ins1 = object1_instances.at(it);
			for (int it2 = 0; it2 < object2_instances.size(); it2++) {
				Instance ins2 = object2_instances.at(it2);
				double matched_prob = 0;
				for (int dim = 1; dim <= p_setting.dimension; dim++) {
					string A1 = ins1.attributes.at(dim - 1);
					string A2 = ins2.attributes.at(dim - 1);
					if (!p_setting.is_digits.at(dim - 1)) {
						//matched_prob += Jaccard_Similarity(A1, A2);
						matched_prob += 1 - Jaccard_Distance(A1, A2);
					}
					else {
						matched_prob += 1 - abs(stod(A1) - stod(A2));
					}
				}
				if (matched_prob > p_setting.gamma) {
					matched_pair_cnt = matched_pair_cnt + ins1.frequency * ins2.frequency;
				}
				checked_pair_cnt = checked_pair_cnt + ins1.frequency * ins2.frequency;

				if ((matched_pair_cnt + total_pair_cnt - checked_pair_cnt) / total_pair_cnt < p_setting.alpha) {
					is_pruned = true;
					break;
				}
			}
			if (is_pruned)
				break;
		}
	}

	return is_pruned;
}

void TER_iDS(vector<vector<Imputed_Data>>& iDS, vector<vector<vector<CDD_Node>>> CDD_index, vector<vector<CDD_Rules>> CDDs, vector<vector<Data>>& data_repository, vector<vector<vector<string>>>& v_domains, vector<vector<R_Node>> R_Nodes, Parameter_Setting p_setting) {// currently, we don't use grid cell in this implementation
	for (int cur_time = 0; cur_time < p_setting.object_max_size; cur_time++) {// this for loop for sliding window
		cout << "current time = " << cur_time << endl;

		int Wt_lower_bound;
		if (cur_time - p_setting.Wt_size < 0)
			Wt_lower_bound = 0;
		else
			Wt_lower_bound = cur_time - p_setting.Wt_size + 1;

		//if (cur_time == 537) {
		//	cout << "debug here --------------" << endl;
		//}

		for (int iDS_1 = 1; iDS_1 <= iDS.size(); iDS_1++) {
			Imputed_Data current_object = iDS.at(iDS_1 - 1).at(cur_time);
			//if (current_object.ID == 1) {
			//	cout << "debug here" << endl;
			//}
			if (current_object.is_incomplete && !current_object.imputed_complete) {
		
				vector<vector<int>> CDDNode_IDs;
				vector<vector<int>> RNode_IDs;

				data_imputation(current_object, CDD_index, CDDs, p_setting.tree_roots.at(iDS_1 - 1), R_Nodes, data_repository, v_domains, false, CDDNode_IDs, RNode_IDs, p_setting);
				data_imputation(current_object, CDD_index, CDDs, p_setting.tree_roots.at(iDS_1 - 1), R_Nodes, data_repository, v_domains, true, CDDNode_IDs, RNode_IDs, p_setting);

				if (current_object.obj_instances.size() == 0) {
					vector<Instance> object1_instances = obtain_instances(current_object, p_setting);
					for (int it = 0; it < object1_instances.size(); it++) {
						current_object.obj_instances.push_back(object1_instances.at(it));
					}
				}

				iDS.at(iDS_1 - 1).at(cur_time) = current_object;// check whether this assignment works
			}
			for (int iDS_2 = 1; iDS_2 <= iDS.size(); iDS_2++) {
				if (iDS_2 != iDS_1) {
					for (int time_temp = Wt_lower_bound; time_temp <= cur_time; time_temp++) {
						Imputed_Data object_compared = iDS.at(iDS_2 - 1).at(time_temp);
						//if (object_compared.is_incomplete) {
						//	cout << "debug here" << endl;
						//}
						if (object_compared.is_incomplete && !object_compared.imputed_complete) {
					
							vector<vector<int>> CDDNode_IDs;
							vector<vector<int>> RNode_IDs;

							data_imputation(object_compared, CDD_index, CDDs, p_setting.tree_roots.at(iDS_2 - 1), R_Nodes, data_repository, v_domains, false, CDDNode_IDs, RNode_IDs, p_setting);
							data_imputation(object_compared, CDD_index, CDDs, p_setting.tree_roots.at(iDS_2 - 1), R_Nodes, data_repository, v_domains, true, CDDNode_IDs, RNode_IDs, p_setting);
							if (object_compared.obj_instances.size() == 0) {
								vector<Instance> object2_instances = obtain_instances(object_compared, p_setting);
								for (int it = 0; it < object2_instances.size(); it++) {
									object_compared.obj_instances.push_back(object2_instances.at(it));
								}
							}
							iDS.at(iDS_2 - 1).at(time_temp) = object_compared;// check whether this assignment works
						}
						//if (cur_time  == 1206 && time_temp == 537) {
						//	cout << "debug here --------------" << endl;
						//	cout << current_object.actual_ID << object_compared.actual_ID << endl;
						//}
						bool is_pruned = Theorems1_4(current_object, object_compared, p_setting);
						if (!is_pruned) {
							if (!check_existance(iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1), object_compared.ID)) {
								iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1).push_back(object_compared.ID);
							}
							if (!check_existance(iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1), current_object.ID)) {
								iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1).push_back(current_object.ID);
							}

						}
					}

				}
				
			}

		}
	}
}

vector<Matching_Record> write_ER_results(vector<vector<Imputed_Data>>& iDS, Parameter_Setting p_setting) {
	vector<Matching_Record> ER_results;
	for (int it = 0; it < iDS.size(); it++) {
		for (int it2 = 0; it2 < iDS.at(it).size(); it2++) {
			Imputed_Data object1 = iDS.at(it).at(it2);
			for (int it3 = 0; it3 < iDS.size(); it3++) {
				if (it3 != it) {
					for (int it4 = 0; it4 < object1.matched_entities.at(it3).size(); it4++) {
						int object2_ID = object1.matched_entities.at(it3).at(it4);
						Imputed_Data object2 = iDS.at(it3).at(object2_ID);
						Matching_Record matching_record;
						matching_record.actual_ID.push_back(object1.actual_ID);
						matching_record.actual_ID.push_back(object2.actual_ID);
						matching_record.iDS_n.push_back(it + 1);
						matching_record.iDS_n.push_back(it3 + 1);

						bool is_recorded = false;
						for (int it5 = 0; it5 < ER_results.size(); it5++) {
							Matching_Record added_record = ER_results.at(it5);
							if ((matching_record.actual_ID.at(0) == added_record.actual_ID.at(0)
								&& matching_record.actual_ID.at(1) == added_record.actual_ID.at(1)
								&& matching_record.iDS_n.at(0) == added_record.iDS_n.at(0)
								&& matching_record.iDS_n.at(1) == added_record.iDS_n.at(1)) ||
								(matching_record.actual_ID.at(0) == added_record.actual_ID.at(1)
									&& matching_record.actual_ID.at(1) == added_record.actual_ID.at(0)
									&& matching_record.iDS_n.at(0) == added_record.iDS_n.at(1)
									&& matching_record.iDS_n.at(1) == added_record.iDS_n.at(0))) {
								is_recorded = true;
								break;
							}
						}

						if (!is_recorded) {
							ER_results.push_back(matching_record);
						}
					}
				}

			}
		}
	}

	ofstream fout(p_setting.ER_result_path, ios::app);
	for (int it = 0; it < ER_results.size(); it++) {
		fout << ER_results.at(it).actual_ID.at(0) << "," << ER_results.at(it).actual_ID.at(1) << "," << ER_results.at(it).iDS_n.at(0) << "," << ER_results.at(it).iDS_n.at(1) << endl;
	}
	fout.close();

	return ER_results;
}

vector<Matching_Record> obtain_ground_truth(Parameter_Setting p_setting) {
	vector<Matching_Record> ground_truth;
	for (int it = 0; it < p_setting.ground_truth_paths.size(); it++) {
		ifstream in(p_setting.ground_truth_paths.at(it));
		string line, attribute;
		//int attribute_cnt;
		int object_cnt = 0;
		int iDS_n1, iDS_n2;
		int attribute_cnt = 0;

		istringstream iss;

		if (in)
		{
			while (getline(in, line))
			{
				iss.clear();
				iss.str(line);
				if (object_cnt == 0) {
					while (getline(iss, attribute, ',')) {
						if (attribute_cnt == 0) {
							iDS_n1 = stoi(attribute);
							attribute_cnt++;
						}
						else {
							iDS_n2 = stoi(attribute);
						}
					}
				}
				else {
					Matching_Record cur_record;
					cur_record.iDS_n.push_back(iDS_n1);
					cur_record.iDS_n.push_back(iDS_n2);
					while (getline(iss, attribute, ',')) {
						cur_record.actual_ID.push_back(attribute);
					}
					ground_truth.push_back(cur_record);
				}
				object_cnt++;
			}

		}
		else
		{
			std::cout << "no such file" << endl;
		}

		in.close();
	}
	return ground_truth;
}

void quality_evaluation(vector<Matching_Record>& ER_Results, vector<Matching_Record>& Ground_Truth, vector<vector<Imputed_Data>>& iDS, Parameter_Setting& p_setting, double cost_per_pair, double cost_for_baselines) {
	int true_positive = 0;
	int false_positive = 0;
	int true_negative = 0;
	int false_negative = 0;
	bool founded;

	vector<int> record_IDs;// record the topic-related valid matching record in ground truth

	/*
	for (int it = 0; it < ER_Results.size(); it++) {// remove the pairs that are not within the sliding window
		bool is_valid_1 = false, is_valid_2 = false;
		string actual_ID1 = ER_Results.at(it).actual_ID.at(0);
		int iDS_n1 = ER_Results.at(it).iDS_n.at(0);
		string actual_ID2 = ER_Results.at(it).actual_ID.at(1);
		int iDS_n2 = ER_Results.at(it).iDS_n.at(1);
		for (int cur_time = 0; cur_time < p_setting.Wt_size; cur_time++) {// this for loop for sliding window
			if (is_valid_1 && is_valid_2)
				break;
			if (iDS.at(iDS_n1 - 1).at(cur_time).actual_ID == actual_ID1)
				is_valid_1 = true;
			if (iDS.at(iDS_n2 - 1).at(cur_time).actual_ID == actual_ID2)
				is_valid_2 = true;
		}
		if (!is_valid_1 || !is_valid_2) {
			ER_Results.erase(ER_Results.begin() + it);
		}
	}
	*/

	for (int it = 0; it < Ground_Truth.size(); it++) {// remove the pairs that are not within the sliding window or not topic-related
		bool is_valid_1 = false, is_valid_2 = false;
		bool is_key_contained_1 = false, is_key_contained_2 = false;
		//bool is_key_initialized_1 = false, is_key_initialized_2 = false;
		int ID_1, ID_2;
		string actual_ID1 = Ground_Truth.at(it).actual_ID.at(0);
		int iDS_n1 = Ground_Truth.at(it).iDS_n.at(0);
		string actual_ID2 = Ground_Truth.at(it).actual_ID.at(1);
		int iDS_n2 = Ground_Truth.at(it).iDS_n.at(1);
		//if (actual_ID2 == "http://www.google.com/base/feeds/snippets/18441110047404795849")
		//	cout << "debug here" << endl;
		for (int cur_time = 0; cur_time < p_setting.object_max_size; cur_time++) {// this for loop for sliding window
			if (is_valid_1 && is_valid_2)
				break;
			if (!is_valid_1 && iDS.at(iDS_n1 - 1).at(cur_time).actual_ID == actual_ID1) {
				is_valid_1 = true;
				ID_1 = cur_time;
			}
				
			if (!is_valid_2 && iDS.at(iDS_n2 - 1).at(cur_time).actual_ID == actual_ID2) {
				is_valid_2 = true;
				ID_2 = cur_time;
			}
		}
		//if (!is_valid_1 || !is_valid_2) {
		//	Ground_Truth.erase(Ground_Truth.begin() + it);
		//}
		if(is_valid_1 && is_valid_2) {// both objects are valid objects
			if (is_valid_1) {
				for (int dim = 1; dim <= p_setting.dimension; dim++) {
					for (int it2 = 0; it2 < iDS.at(iDS_n1 - 1).at(ID_1).possible_values.at(dim - 1).size(); it2++) {
						string val_string = iDS.at(iDS_n1 - 1).at(ID_1).possible_values.at(dim - 1).at(it2);
						for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
							if (val_string.find(p_setting.keywords.at(it3)) != std::string::npos) {
								is_key_contained_1 = true;
								//is_key_initialized_1 = true;
								break;
							}
						}
						if (is_key_contained_1)
							break;
					}
					if (is_key_contained_1)
						break;
				}
			}

			if (is_valid_2) {
				for (int dim = 1; dim <= p_setting.dimension; dim++) {
					for (int it2 = 0; it2 < iDS.at(iDS_n2 - 1).at(ID_2).possible_values.at(dim - 1).size(); it2++) {
						string val_string = iDS.at(iDS_n2 - 1).at(ID_2).possible_values.at(dim - 1).at(it2);
						for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
							if (val_string.find(p_setting.keywords.at(it3)) != std::string::npos) {
								is_key_contained_2 = true;
								//is_key_initialized_2 = true;
								break;
							}
						}
						if (is_key_contained_2)
							break;
					}
					if (is_key_contained_2)
						break;
				}
			}

			//if(!is_key_contained_1 && !is_key_contained_2)
			//	Ground_Truth.erase(Ground_Truth.begin() + it);
			if (is_key_contained_1 || is_key_contained_2)
				record_IDs.push_back(it);
		}
	}

	for (int it = 0; it < record_IDs.size(); it++) {
		Matching_Record record_1 = Ground_Truth.at(record_IDs.at(it));
		bool is_founded = false;
		for (int it2 = 0; it2 < ER_Results.size(); it2++) {
			Matching_Record record_2 = ER_Results.at(it2);
			if ((record_1.iDS_n.at(0) == record_2.iDS_n.at(0) && record_1.iDS_n.at(1) == record_2.iDS_n.at(1) && record_1.actual_ID.at(0) == record_2.actual_ID.at(0) && record_1.actual_ID.at(1) == record_2.actual_ID.at(1))
				||
				(record_1.iDS_n.at(0) == record_2.iDS_n.at(1) && record_1.iDS_n.at(1) == record_2.iDS_n.at(0) && record_1.actual_ID.at(0) == record_2.actual_ID.at(1) && record_1.actual_ID.at(1) == record_2.actual_ID.at(0))) {
				true_positive++;
				is_founded = true;
				break;
			}
		}
		if (!is_founded)
			false_negative++;
	}

	std::cout << "the number of ground truth are : " << record_IDs.size() << endl;
	std::cout << "the number of returned answers are : " << ER_Results.size() << endl;

	std::cout << "true positive = " << true_positive << endl;
	std::cout << "false negative = " << false_negative << endl;

	false_positive = ER_Results.size() - true_positive;

	std::cout << "false positive = " << false_positive << endl;

	double recall = (double)true_positive / (true_positive + false_negative);
	double precision = (double)true_positive / (true_positive + false_positive);
	double F1_score = (2 * recall * precision) / (recall + precision);

	ofstream fout(p_setting.quality_evaluation_path, ios::app);
	fout << "the number of ground truth are : " << record_IDs.size() << endl;
	fout << "the number of returned answers are : " << ER_Results.size() << endl;

	fout << "true positive = " << true_positive << endl;
	fout << "false negative = " << false_negative << endl;

	false_positive = ER_Results.size() - true_positive;

	fout << "false positive = " << false_positive << endl;

	fout << "recall = " << recall << endl;
	fout << "precision = " << precision << endl;
	fout << "F1 Score = " << F1_score << endl;
	fout << "time cost per entity pair ---->" << cost_per_pair << endl;
	fout << "add this cost for baselines (per pair) --------------->" << cost_for_baselines << endl;

	fout.close();
}

void CDD_ER(vector<vector<Imputed_Data>>& iDS, vector<vector<Data>>& data_repository, vector<vector<CDD_Rules>> CDDs, Parameter_Setting p_setting) {// solve the TER-iDS problem without pruning and indexes
	for (int cur_time = 0; cur_time < p_setting.object_max_size; cur_time++) {// this for loop for sliding window
		cout << "current time = " << cur_time << endl;
		//if (cur_time == 1409)
		//	cout << "debug here" << endl;

		int Wt_lower_bound;
		if (cur_time - p_setting.Wt_size < 0)
			Wt_lower_bound = 0;
		else
			Wt_lower_bound = cur_time - p_setting.Wt_size + 1;

		for (int iDS_1 = 1; iDS_1 <= iDS.size(); iDS_1++) {
			Imputed_Data current_object = iDS.at(iDS_1 - 1).at(cur_time);

			if (current_object.is_incomplete && !current_object.imputed_complete) {

				vector<vector<int>> available_CDD_IDs;
				vector<int> available_CDD_IDs_temp;

				for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// find out all avaliable CDDs for imputing incomplete objects
					available_CDD_IDs_temp.clear();
					int missing_attribute = p_setting.missing_attributes.at(it);
					int value_attribute = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).value_attribute;
					int interval_attribute = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).interval_attribute;
					for (int it2 = 0; it2 < CDDs.at(iDS_1 - 1).at(missing_attribute - 1).Ax_values.size(); it2++) {
						string constraint_value = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).Ax_values.at(it2);
						if (current_object.possible_values.at(value_attribute - 1).at(0) == constraint_value) {// constraint values are satisfied, this CDD can be adopted
							available_CDD_IDs_temp.push_back(it2);
						}
					}
					available_CDD_IDs.push_back(available_CDD_IDs_temp);
				}

				for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using retrieved CDDs
					int missing_attribute = p_setting.missing_attributes.at(it);
					int value_attribute = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).value_attribute;
					int interval_attribute = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).interval_attribute;
					for (int it2 = 0; it2 < available_CDD_IDs.at(it).size(); it2++) {
						int cur_CDD_ID = available_CDD_IDs.at(it).at(it2);
						for (int it3 = 0; it3 < data_repository.at(iDS_1 - 1).size(); it3++) {
							//if (it3 == 10 || it3 == 224)
							//	cout << "debug here" << endl;
							if (current_object.possible_values.at(value_attribute - 1).at(0) == data_repository.at(iDS_1 - 1).at(it3).attributes.at(value_attribute - 1)) {// constraint value matches
								double dist_temp;
								if (p_setting.is_digits.at(interval_attribute - 1)) {
									dist_temp = stod(current_object.possible_values.at(interval_attribute - 1).at(0)) - stod(data_repository.at(iDS_1 - 1).at(it3).attributes.at(interval_attribute - 1));
								}
								else {
									dist_temp = Jaccard_Distance(current_object.possible_values.at(interval_attribute - 1).at(0), data_repository.at(iDS_1 - 1).at(it3).attributes.at(interval_attribute - 1));
								}
								if (dist_temp <= CDDs.at(iDS_1 - 1).at(missing_attribute - 1).Ax_interval) {// interval constraints satisfies, this complete data can be used for imputing
									string possible_value = data_repository.at(iDS_1 - 1).at(it3).attributes.at(missing_attribute - 1);
									bool is_found_temp = false;
									for (int it4 = 0; it4 < current_object.possible_values.at(missing_attribute - 1).size(); it4++) {
										if (current_object.possible_values.at(missing_attribute - 1).at(it4) == possible_value) {
											current_object.value_frequency.at(missing_attribute - 1).at(it4) += 1;
											is_found_temp = true;
											break;
										}
									}
									if (!is_found_temp) {
										current_object.possible_values.at(missing_attribute - 1).push_back(possible_value);
										current_object.value_frequency.at(missing_attribute - 1).push_back(1);
									}
								}
							}
						}
					}
				
					if (current_object.possible_values.at(missing_attribute - 1).size() == 0) {//imputation fails, no suitable values found
						if (p_setting.is_digits.at(missing_attribute - 1)) {
							current_object.possible_values.at(missing_attribute - 1).push_back(to_string(-1));
						}
						else {
							current_object.possible_values.at(missing_attribute - 1).push_back("not found");
						}
						current_object.value_frequency.at(missing_attribute - 1).push_back(1);
					}
				}

				current_object.imputed_complete = true;

				if (current_object.obj_instances.size() == 0) {
					vector<Instance> object1_instances = obtain_instances(current_object, p_setting);
					for (int it = 0; it < object1_instances.size(); it++) {
						current_object.obj_instances.push_back(object1_instances.at(it));
					}
				}

				iDS.at(iDS_1 - 1).at(cur_time) = current_object;// check whether this assignment works
			}
			for (int iDS_2 = 1; iDS_2 <= iDS.size(); iDS_2++) {
				if (iDS_2 != iDS_1) {
					for (int time_temp = Wt_lower_bound; time_temp <= cur_time; time_temp++) {
						//if (time_temp == 1409)
						//	cout << "debug here" << endl;

						Imputed_Data object_compared = iDS.at(iDS_2 - 1).at(time_temp);

						if (object_compared.is_incomplete && !object_compared.imputed_complete) {

							vector<vector<int>> available_CDD_IDs;
							vector<int> available_CDD_IDs_temp;

							for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// find out all avaliable CDDs for imputing incomplete objects
								available_CDD_IDs_temp.clear();
								int missing_attribute = p_setting.missing_attributes.at(it);
								int value_attribute = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).value_attribute;
								int interval_attribute = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).interval_attribute;
								for (int it2 = 0; it2 < CDDs.at(iDS_2 - 1).at(missing_attribute - 1).Ax_values.size(); it2++) {
									string constraint_value = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).Ax_values.at(it2);
									if (object_compared.possible_values.at(value_attribute - 1).at(0) == constraint_value) {// constraint values are satisfied, this CDD can be adopted
										available_CDD_IDs_temp.push_back(it2);
									}
								}
								available_CDD_IDs.push_back(available_CDD_IDs_temp);
							}

							for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using retrieved CDDs
								int missing_attribute = p_setting.missing_attributes.at(it);
								int value_attribute = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).value_attribute;
								int interval_attribute = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).interval_attribute;
								for (int it2 = 0; it2 < available_CDD_IDs.at(it).size(); it2++) {
									int cur_CDD_ID = available_CDD_IDs.at(it).at(it2);
									for (int it3 = 0; it3 < data_repository.at(iDS_2 - 1).size(); it3++) {
										if (object_compared.possible_values.at(value_attribute - 1).at(0) == data_repository.at(iDS_2 - 1).at(it3).attributes.at(value_attribute - 1)) {// constraint value matches
											double dist_temp;
											if (p_setting.is_digits.at(interval_attribute - 1)) {
												dist_temp = stod(object_compared.possible_values.at(interval_attribute - 1).at(0)) - stod(data_repository.at(iDS_2 - 1).at(it3).attributes.at(interval_attribute - 1));
											}
											else {
												dist_temp = Jaccard_Distance(object_compared.possible_values.at(interval_attribute - 1).at(0), data_repository.at(iDS_2 - 1).at(it3).attributes.at(interval_attribute - 1));
											}
											if (dist_temp <= CDDs.at(iDS_2 - 1).at(missing_attribute - 1).Ax_interval) {// interval constraints satisfies, this complete data can be used for imputing
												string possible_value = data_repository.at(iDS_2 - 1).at(it3).attributes.at(missing_attribute - 1);
												bool is_found_temp = false;
												for (int it4 = 0; it4 < object_compared.possible_values.at(missing_attribute - 1).size(); it4++) {
													if (object_compared.possible_values.at(missing_attribute - 1).at(it4) == possible_value) {
														object_compared.value_frequency.at(missing_attribute - 1).at(it4) += 1;
														is_found_temp = true;
														break;
													}
												}
												if (!is_found_temp) {
													object_compared.possible_values.at(missing_attribute - 1).push_back(possible_value);
													object_compared.value_frequency.at(missing_attribute - 1).push_back(1);
												}
											}
										}
									}
								}
							
								if (object_compared.possible_values.at(missing_attribute - 1).size() == 0) {//imputation fails, no suitable values found
									if (p_setting.is_digits.at(missing_attribute - 1)) {
										object_compared.possible_values.at(missing_attribute - 1).push_back(to_string(-1));
									}
									else {
										object_compared.possible_values.at(missing_attribute - 1).push_back("not found");
									}
									object_compared.value_frequency.at(missing_attribute - 1).push_back(1);
								}
							}

							object_compared.imputed_complete = true;


							if (object_compared.obj_instances.size() == 0) {
								vector<Instance> object2_instances = obtain_instances(object_compared, p_setting);
								for (int it = 0; it < object2_instances.size(); it++) {
									object_compared.obj_instances.push_back(object2_instances.at(it));
								}
							}
							iDS.at(iDS_2 - 1).at(time_temp) = object_compared;// check whether this assignment works
						}

						// start from here, checking pairs
						vector<Instance> object1_instances = current_object.obj_instances;
						vector<Instance> object2_instances = object_compared.obj_instances;
						int checked_pair_cnt = 0, matched_pair_cnt = 0;
						int ins_freq_cnt1 = 0, ins_freq_cnt2 = 0;
						for (int it = 0; it < object1_instances.size(); it++) {
							ins_freq_cnt1 = ins_freq_cnt1 + object1_instances.at(it).frequency;
						}
						for (int it = 0; it < object2_instances.size(); it++) {
							ins_freq_cnt2 = ins_freq_cnt2 + object2_instances.at(it).frequency;
						}
						double total_pair_cnt = ins_freq_cnt1 * ins_freq_cnt2;
						for (int it = 0; it < object1_instances.size(); it++) {
							Instance ins1 = object1_instances.at(it);
							for (int it2 = 0; it2 < object2_instances.size(); it2++) {
								Instance ins2 = object2_instances.at(it2);
								double matched_prob = 0;
								for (int dim = 1; dim <= p_setting.dimension; dim++) {
									string A1 = ins1.attributes.at(dim - 1);
									string A2 = ins2.attributes.at(dim - 1);
									if (!p_setting.is_digits.at(dim - 1)) {
										//matched_prob += Jaccard_Similarity(A1, A2);
										matched_prob += 1 - Jaccard_Distance(A1, A2);
									}
									else {
										matched_prob += 1 - abs(stod(A1) - stod(A2));
									}
								}
								if (matched_prob > p_setting.gamma) {
									matched_pair_cnt = matched_pair_cnt + ins1.frequency * ins2.frequency;
								}
								//checked_pair_cnt = checked_pair_cnt + ins1.frequency * ins2.frequency;
							}

						}

						if (matched_pair_cnt / total_pair_cnt >= p_setting.alpha) {// pair matching, further checking whether or not topic-related
							bool is_topic_related = false;
							for (int it = 0; it < object1_instances.size(); it++) {
								for (int it2 = 1; it2 < p_setting.dimension; it2++) {
									for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
										if (object1_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
											is_topic_related = true;
											break;
										}
									}
									if (is_topic_related)
										break;
								}
								if (is_topic_related)
									break;
							}

							if (!is_topic_related) {
								for (int it = 0; it < object2_instances.size(); it++) {
									for (int it2 = 1; it2 < p_setting.dimension; it2++) {
										for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
											if (object2_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
												is_topic_related = true;
												break;
											}
										}
										if (is_topic_related)
											break;
									}
									if (is_topic_related)
										break;
								}
							}

							if (is_topic_related) {
								if (!check_existance(iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1), object_compared.ID)) {
									iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1).push_back(object_compared.ID);
								}
								if (!check_existance(iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1), current_object.ID)) {
									iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1).push_back(current_object.ID);
								}

							}
						}
					}

				}

			}

		}
	}

}

void Ij_GER(vector<vector<Imputed_Data>>& iDS, vector<vector<vector<CDD_Node>>> CDD_index, vector<vector<CDD_Rules>> CDDs, vector<vector<Data>>& data_repository, vector<vector<vector<string>>>& v_domains, vector<vector<R_Node>> R_Nodes, Parameter_Setting p_setting) {
	cout << "-------------------imputation------------------------------" << endl;
	for (int iDS_n = 1; iDS_n <= iDS.size(); iDS_n++) {// imputation
		for (int it = 0; it < iDS.at(iDS_n - 1).size(); it++) {
			//if (iDS_n == 2 && it == 1409)
			//	cout << "debug here" << endl;
			Imputed_Data current_object = iDS.at(iDS_n - 1).at(it);
			if (current_object.is_incomplete && !current_object.imputed_complete) {
				vector<vector<int>> CDDNode_IDs;
				vector<vector<int>> RNode_IDs;
				data_imputation(current_object, CDD_index, CDDs, p_setting.tree_roots.at(iDS_n - 1), R_Nodes, data_repository, v_domains, false, CDDNode_IDs, RNode_IDs, p_setting);
				data_imputation(current_object, CDD_index, CDDs, p_setting.tree_roots.at(iDS_n - 1), R_Nodes, data_repository, v_domains, true, CDDNode_IDs, RNode_IDs, p_setting);
				if (current_object.obj_instances.size() == 0) {
					vector<Instance> object1_instances = obtain_instances(current_object, p_setting);
					for (int it = 0; it < object1_instances.size(); it++) {
						current_object.obj_instances.push_back(object1_instances.at(it));
					}
				}
				iDS.at(iDS_n - 1).at(it) = current_object;
			}
		}

	}

	cout << "----------------ER query----------------------------------------------" << endl;
	for (int cur_time = 0; cur_time < p_setting.object_max_size; cur_time++) {// ER query
		cout << "current time = " << cur_time << endl;

		int Wt_lower_bound;
		if (cur_time - p_setting.Wt_size < 0)
			Wt_lower_bound = 0;
		else
			Wt_lower_bound = cur_time - p_setting.Wt_size + 1;

		for (int iDS_1 = 1; iDS_1 <= iDS.size(); iDS_1++) {
			Imputed_Data current_object = iDS.at(iDS_1 - 1).at(cur_time);
			for (int iDS_2 = 1; iDS_2 <= iDS.size(); iDS_2++) {
				if (iDS_2 != iDS_1) {
					for (int time_temp = Wt_lower_bound; time_temp <= cur_time; time_temp++) {
						Imputed_Data object_compared = iDS.at(iDS_2 - 1).at(time_temp);

						bool is_pruned = Theorems1_4(current_object, object_compared, p_setting);
						if (!is_pruned) {
							if (!check_existance(iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1), object_compared.ID)) {
								iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1).push_back(object_compared.ID);
							}
							if (!check_existance(iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1), current_object.ID)) {
								iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1).push_back(current_object.ID);
							}

						}
					}

				}

			}

		}
	}

}

void DD_ER(vector<vector<Imputed_Data>>& iDS, vector<vector<Data>>& data_repository, vector<vector<CDD_Rules>> CDDs, Parameter_Setting p_setting) {// we use Ax_interval for both constraint attribute and interval attribute in this implementation
	for (int cur_time = 0; cur_time < p_setting.object_max_size; cur_time++) {// this for loop for sliding window
		cout << "current time = " << cur_time << endl;

		int Wt_lower_bound;
		if (cur_time - p_setting.Wt_size < 0)
			Wt_lower_bound = 0;
		else
			Wt_lower_bound = cur_time - p_setting.Wt_size + 1;

		for (int iDS_1 = 1; iDS_1 <= iDS.size(); iDS_1++) {
			Imputed_Data current_object = iDS.at(iDS_1 - 1).at(cur_time);
			if (current_object.is_incomplete && !current_object.imputed_complete) {
				for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using DDs
					int missing_attribute = p_setting.missing_attributes.at(it);
					int value_attribute = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).value_attribute;
					int interval_attribute = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).interval_attribute;

					for (int it3 = 0; it3 < data_repository.at(iDS_1 - 1).size(); it3++) {
						double dist_temp;
						if (p_setting.is_digits.at(value_attribute - 1)) {
							dist_temp = stod(current_object.possible_values.at(value_attribute - 1).at(0)) - stod(data_repository.at(iDS_1 - 1).at(it3).attributes.at(value_attribute - 1));
						}
						else {
							dist_temp = Jaccard_Distance(current_object.possible_values.at(value_attribute - 1).at(0), data_repository.at(iDS_1 - 1).at(it3).attributes.at(value_attribute - 1));
						}
						bool is_further_check = false;
						if (dist_temp <= CDDs.at(iDS_1 - 1).at(missing_attribute - 1).Ax_interval)
							is_further_check = true;

						if (is_further_check) { // constraint constraints for DD
							double dist_temp;
							if (p_setting.is_digits.at(interval_attribute - 1)) {
								dist_temp = stod(current_object.possible_values.at(interval_attribute - 1).at(0)) - stod(data_repository.at(iDS_1 - 1).at(it3).attributes.at(interval_attribute - 1));
							}
							else {
								dist_temp = Jaccard_Distance(current_object.possible_values.at(interval_attribute - 1).at(0), data_repository.at(iDS_1 - 1).at(it3).attributes.at(interval_attribute - 1));
							}
							if (dist_temp <= CDDs.at(iDS_1 - 1).at(missing_attribute - 1).Ax_interval) {// interval constraints satisfies, this complete data can be used for imputing
								string possible_value = data_repository.at(iDS_1 - 1).at(it3).attributes.at(missing_attribute - 1);
								bool is_found_temp = false;
								for (int it4 = 0; it4 < current_object.possible_values.at(missing_attribute - 1).size(); it4++) {
									if (current_object.possible_values.at(missing_attribute - 1).at(it4) == possible_value) {
										current_object.value_frequency.at(missing_attribute - 1).at(it4) += 1;
										is_found_temp = true;
										break;
									}
								}
								if (!is_found_temp) {
									current_object.possible_values.at(missing_attribute - 1).push_back(possible_value);
									current_object.value_frequency.at(missing_attribute - 1).push_back(1);
								}
							}
						}
					}
				}

				current_object.imputed_complete = true;

				if (current_object.obj_instances.size() == 0) {
					vector<Instance> object1_instances = obtain_instances(current_object, p_setting);
					for (int it = 0; it < object1_instances.size(); it++) {
						current_object.obj_instances.push_back(object1_instances.at(it));
					}
				}

				iDS.at(iDS_1 - 1).at(cur_time) = current_object;
			}
			for (int iDS_2 = 1; iDS_2 <= iDS.size(); iDS_2++) {
				if (iDS_2 != iDS_1) {
					for (int time_temp = Wt_lower_bound; time_temp <= cur_time; time_temp++) {
						Imputed_Data object_compared = iDS.at(iDS_2 - 1).at(time_temp);
						if (object_compared.is_incomplete && !object_compared.imputed_complete) {
							for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using retrieved CDDs
								int missing_attribute = p_setting.missing_attributes.at(it);
								int value_attribute = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).value_attribute;
								int interval_attribute = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).interval_attribute;
								for (int it3 = 0; it3 < data_repository.at(iDS_2 - 1).size(); it3++) {
									double dist_temp;
									if (p_setting.is_digits.at(value_attribute - 1)) {
										dist_temp = stod(object_compared.possible_values.at(value_attribute - 1).at(0)) - stod(data_repository.at(iDS_2 - 1).at(it3).attributes.at(value_attribute - 1));
									}
									else {
										dist_temp = Jaccard_Distance(object_compared.possible_values.at(value_attribute - 1).at(0), data_repository.at(iDS_2 - 1).at(it3).attributes.at(value_attribute - 1));
									}
									bool is_further_check = false;
									if (dist_temp <= CDDs.at(iDS_2 - 1).at(missing_attribute - 1).Ax_interval)
										is_further_check = true;

									if (is_further_check) {// constraint value matches
										double dist_temp;
										if (p_setting.is_digits.at(interval_attribute - 1)) {
											dist_temp = stod(object_compared.possible_values.at(interval_attribute - 1).at(0)) - stod(data_repository.at(iDS_2 - 1).at(it3).attributes.at(interval_attribute - 1));
										}
										else {
											dist_temp = Jaccard_Distance(object_compared.possible_values.at(interval_attribute - 1).at(0), data_repository.at(iDS_2 - 1).at(it3).attributes.at(interval_attribute - 1));
										}
										if (dist_temp <= CDDs.at(iDS_2 - 1).at(missing_attribute - 1).Ax_interval) {// interval constraints satisfies, this complete data can be used for imputing
											string possible_value = data_repository.at(iDS_2 - 1).at(it3).attributes.at(missing_attribute - 1);
											bool is_found_temp = false;
											for (int it4 = 0; it4 < object_compared.possible_values.at(missing_attribute - 1).size(); it4++) {
												if (object_compared.possible_values.at(missing_attribute - 1).at(it4) == possible_value) {
													object_compared.value_frequency.at(missing_attribute - 1).at(it4) += 1;
													is_found_temp = true;
													break;
												}
											}
											if (!is_found_temp) {
												object_compared.possible_values.at(missing_attribute - 1).push_back(possible_value);
												object_compared.value_frequency.at(missing_attribute - 1).push_back(1);
											}
										}
									}
								}
							}

							object_compared.imputed_complete = true;


							if (object_compared.obj_instances.size() == 0) {
								vector<Instance> object2_instances = obtain_instances(object_compared, p_setting);
								for (int it = 0; it < object2_instances.size(); it++) {
									object_compared.obj_instances.push_back(object2_instances.at(it));
								}
							}
							iDS.at(iDS_2 - 1).at(time_temp) = object_compared;// check whether this assignment works
						}

						// start from here, checking pairs
						vector<Instance> object1_instances = current_object.obj_instances;
						vector<Instance> object2_instances = object_compared.obj_instances;
						int checked_pair_cnt = 0, matched_pair_cnt = 0;
						int ins_freq_cnt1 = 0, ins_freq_cnt2 = 0;
						for (int it = 0; it < object1_instances.size(); it++) {
							ins_freq_cnt1 = ins_freq_cnt1 + object1_instances.at(it).frequency;
						}
						for (int it = 0; it < object2_instances.size(); it++) {
							ins_freq_cnt2 = ins_freq_cnt2 + object2_instances.at(it).frequency;
						}
						double total_pair_cnt = ins_freq_cnt1 * ins_freq_cnt2;
						for (int it = 0; it < object1_instances.size(); it++) {
							Instance ins1 = object1_instances.at(it);
							for (int it2 = 0; it2 < object2_instances.size(); it2++) {
								Instance ins2 = object2_instances.at(it2);
								double matched_prob = 0;
								for (int dim = 1; dim <= p_setting.dimension; dim++) {
									string A1 = ins1.attributes.at(dim - 1);
									string A2 = ins2.attributes.at(dim - 1);
									if (!p_setting.is_digits.at(dim - 1)) {
										//matched_prob += Jaccard_Similarity(A1, A2);
										matched_prob += 1 - Jaccard_Distance(A1, A2);
									}
									else {
										matched_prob += 1 - abs(stod(A1) - stod(A2));
									}
								}
								if (matched_prob > p_setting.gamma) {
									matched_pair_cnt = matched_pair_cnt + ins1.frequency * ins2.frequency;
								}
								//checked_pair_cnt = checked_pair_cnt + ins1.frequency * ins2.frequency;
							}

						}

						if (matched_pair_cnt / total_pair_cnt >= p_setting.alpha) {// pair matching, further checking whether or not topic-related
							bool is_topic_related = false;
							for (int it = 0; it < object1_instances.size(); it++) {
								for (int it2 = 1; it2 < p_setting.dimension; it2++) {
									for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
										if (object1_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
											is_topic_related = true;
											break;
										}
									}
									if (is_topic_related)
										break;
								}
								if (is_topic_related)
									break;
							}

							if (!is_topic_related) {
								for (int it = 0; it < object2_instances.size(); it++) {
									for (int it2 = 1; it2 < p_setting.dimension; it2++) {
										for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
											if (object2_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
												is_topic_related = true;
												break;
											}
										}
										if (is_topic_related)
											break;
									}
									if (is_topic_related)
										break;
								}
							}

							if (is_topic_related) {
								if (!check_existance(iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1), object_compared.ID)) {
									iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1).push_back(object_compared.ID);
								}
								if (!check_existance(iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1), current_object.ID)) {
									iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1).push_back(current_object.ID);
								}

							}
						}
					}

				}

			}

		}
	}

}

void con_ER(vector<vector<Imputed_Data>>& iDS, Parameter_Setting p_setting) {
	for (int cur_time = 0; cur_time < p_setting.object_max_size; cur_time++) {// this for loop for sliding window
		cout << "current time = " << cur_time << endl;

		int Wt_lower_bound;
		if (cur_time - p_setting.Wt_size < 0)
			Wt_lower_bound = 0;
		else
			Wt_lower_bound = cur_time - p_setting.Wt_size + 1;

		for (int iDS_1 = 1; iDS_1 <= iDS.size(); iDS_1++) {
			Imputed_Data current_object = iDS.at(iDS_1 - 1).at(cur_time);
			if (current_object.is_incomplete && !current_object.imputed_complete) {
				for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using last observed value
					int missing_attribute = p_setting.missing_attributes.at(it);
					if (cur_time > 0)
						current_object.possible_values.at(missing_attribute - 1).push_back(iDS.at(iDS_1 - 1).at(cur_time - 1).possible_values.at(missing_attribute - 1).at(0));
					current_object.value_frequency.at(missing_attribute - 1).push_back(1);
				}

				current_object.imputed_complete = true;

				if (current_object.obj_instances.size() == 0) {
					vector<Instance> object1_instances = obtain_instances(current_object, p_setting);
					for (int it = 0; it < object1_instances.size(); it++) {
						current_object.obj_instances.push_back(object1_instances.at(it));
					}
				}
				iDS.at(iDS_1 - 1).at(cur_time) = current_object;
			}
			for (int iDS_2 = 1; iDS_2 <= iDS.size(); iDS_2++) {
				if (iDS_2 != iDS_1) {
					for (int time_temp = Wt_lower_bound; time_temp <= cur_time; time_temp++) {
						Imputed_Data object_compared = iDS.at(iDS_2 - 1).at(time_temp);
						if (object_compared.is_incomplete && !object_compared.imputed_complete) {
							for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using last observed value
								int missing_attribute = p_setting.missing_attributes.at(it);
								if (time_temp > 0)
									object_compared.possible_values.at(missing_attribute - 1).push_back(iDS.at(iDS_2 - 1).at(time_temp - 1).possible_values.at(missing_attribute - 1).at(0));
								object_compared.value_frequency.at(missing_attribute - 1).push_back(1);
							}
							object_compared.imputed_complete = true;
							if (object_compared.obj_instances.size() == 0) {
								vector<Instance> object2_instances = obtain_instances(object_compared, p_setting);
								for (int it = 0; it < object2_instances.size(); it++) {
									object_compared.obj_instances.push_back(object2_instances.at(it));
								}
							}
							iDS.at(iDS_2 - 1).at(time_temp) = object_compared;// check whether this assignment works
						}

						// start from here, checking pairs
						vector<Instance> object1_instances = current_object.obj_instances;
						vector<Instance> object2_instances = object_compared.obj_instances;
						int checked_pair_cnt = 0, matched_pair_cnt = 0;
						int ins_freq_cnt1 = 0, ins_freq_cnt2 = 0;
						for (int it = 0; it < object1_instances.size(); it++) {
							ins_freq_cnt1 = ins_freq_cnt1 + object1_instances.at(it).frequency;
						}
						for (int it = 0; it < object2_instances.size(); it++) {
							ins_freq_cnt2 = ins_freq_cnt2 + object2_instances.at(it).frequency;
						}
						double total_pair_cnt = ins_freq_cnt1 * ins_freq_cnt2;
						for (int it = 0; it < object1_instances.size(); it++) {
							Instance ins1 = object1_instances.at(it);
							for (int it2 = 0; it2 < object2_instances.size(); it2++) {
								Instance ins2 = object2_instances.at(it2);
								double matched_prob = 0;
								for (int dim = 1; dim <= p_setting.dimension; dim++) {
									string A1 = ins1.attributes.at(dim - 1);
									string A2 = ins2.attributes.at(dim - 1);
									if (!p_setting.is_digits.at(dim - 1)) {
										//matched_prob += Jaccard_Similarity(A1, A2);
										matched_prob += 1 - Jaccard_Distance(A1, A2);
									}
									else {
										matched_prob += 1 - abs(stod(A1) - stod(A2));
									}
								}
								if (matched_prob > p_setting.gamma) {
									matched_pair_cnt = matched_pair_cnt + ins1.frequency * ins2.frequency;
								}
								//checked_pair_cnt = checked_pair_cnt + ins1.frequency * ins2.frequency;
							}

						}

						if (matched_pair_cnt / total_pair_cnt >= p_setting.alpha) {// pair matching, further checking whether or not topic-related
							bool is_topic_related = false;
							for (int it = 0; it < object1_instances.size(); it++) {
								for (int it2 = 1; it2 < p_setting.dimension; it2++) {
									for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
										if (object1_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
											is_topic_related = true;
											break;
										}
									}
									if (is_topic_related)
										break;
								}
								if (is_topic_related)
									break;
							}

							if (!is_topic_related) {
								for (int it = 0; it < object2_instances.size(); it++) {
									for (int it2 = 1; it2 < p_setting.dimension; it2++) {
										for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
											if (object2_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
												is_topic_related = true;
												break;
											}
										}
										if (is_topic_related)
											break;
									}
									if (is_topic_related)
										break;
								}
							}

							if (is_topic_related) {
								if (!check_existance(iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1), object_compared.ID)) {
									iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1).push_back(object_compared.ID);
								}
								if (!check_existance(iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1), current_object.ID)) {
									iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1).push_back(current_object.ID);
								}

							}
						}
					}

				}

			}

		}
	}

}

void er_ER(vector<vector<Imputed_Data>>& iDS, vector<vector<Data>>& data_repository, vector<vector<CDD_Rules>> CDDs, Parameter_Setting p_setting) {
	for (int cur_time = 0; cur_time < p_setting.object_max_size; cur_time++) {// this for loop for sliding window
		cout << "current time = " << cur_time << endl;
		int Wt_lower_bound;
		if (cur_time - p_setting.Wt_size < 0)
			Wt_lower_bound = 0;
		else
			Wt_lower_bound = cur_time - p_setting.Wt_size + 1;

		for (int iDS_1 = 1; iDS_1 <= iDS.size(); iDS_1++) {
			Imputed_Data current_object = iDS.at(iDS_1 - 1).at(cur_time);

			if (current_object.is_incomplete && !current_object.imputed_complete) {
				for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using editing rule
					int missing_attribute = p_setting.missing_attributes.at(it);
					int value_attribute = CDDs.at(iDS_1 - 1).at(missing_attribute - 1).value_attribute;

					for (int it3 = 0; it3 < data_repository.at(iDS_1 - 1).size(); it3++) {
						if (current_object.possible_values.at(value_attribute - 1).at(0) == data_repository.at(iDS_1 - 1).at(it3).attributes.at(value_attribute - 1)) {// constraint value matches
							string possible_value = data_repository.at(iDS_1 - 1).at(it3).attributes.at(missing_attribute - 1);
							if (current_object.possible_values.at(value_attribute - 1).size() == 0) {
								current_object.possible_values.at(missing_attribute - 1).push_back(possible_value);
							}

						}
					}

					current_object.value_frequency.at(missing_attribute - 1).push_back(1);
				}

				current_object.imputed_complete = true;

				if (current_object.obj_instances.size() == 0) {
					vector<Instance> object1_instances = obtain_instances(current_object, p_setting);
					for (int it = 0; it < object1_instances.size(); it++) {
						current_object.obj_instances.push_back(object1_instances.at(it));
					}
				}

				iDS.at(iDS_1 - 1).at(cur_time) = current_object;// check whether this assignment works
			}
			for (int iDS_2 = 1; iDS_2 <= iDS.size(); iDS_2++) {
				if (iDS_2 != iDS_1) {
					for (int time_temp = Wt_lower_bound; time_temp <= cur_time; time_temp++) {
						Imputed_Data object_compared = iDS.at(iDS_2 - 1).at(time_temp);

						if (object_compared.is_incomplete && !object_compared.imputed_complete) {
							for (int it = 0; it < p_setting.missing_attributes.size(); it++) {// impute attribute, using editing rule
								int missing_attribute = p_setting.missing_attributes.at(it);
								int value_attribute = CDDs.at(iDS_2 - 1).at(missing_attribute - 1).value_attribute;

								for (int it3 = 0; it3 < data_repository.at(iDS_2 - 1).size(); it3++) {
									if (object_compared.possible_values.at(value_attribute - 1).at(0) == data_repository.at(iDS_2 - 1).at(it3).attributes.at(value_attribute - 1)) {// constraint value matches
										string possible_value = data_repository.at(iDS_2 - 1).at(it3).attributes.at(missing_attribute - 1);
										if (object_compared.possible_values.at(missing_attribute - 1).size() == 0) {
											object_compared.possible_values.at(missing_attribute - 1).push_back(possible_value);
										}
									}
								}
								object_compared.value_frequency.at(missing_attribute - 1).push_back(1);
							}

							object_compared.imputed_complete = true;

							if (object_compared.obj_instances.size() == 0) {
								vector<Instance> object2_instances = obtain_instances(object_compared, p_setting);
								for (int it = 0; it < object2_instances.size(); it++) {
									object_compared.obj_instances.push_back(object2_instances.at(it));
								}
							}
							iDS.at(iDS_2 - 1).at(time_temp) = object_compared;// check whether this assignment works
						}

						// start from here, checking pairs
						vector<Instance> object1_instances = current_object.obj_instances;
						vector<Instance> object2_instances = object_compared.obj_instances;
						int checked_pair_cnt = 0, matched_pair_cnt = 0;
						int ins_freq_cnt1 = 0, ins_freq_cnt2 = 0;
						for (int it = 0; it < object1_instances.size(); it++) {
							ins_freq_cnt1 = ins_freq_cnt1 + object1_instances.at(it).frequency;
						}
						for (int it = 0; it < object2_instances.size(); it++) {
							ins_freq_cnt2 = ins_freq_cnt2 + object2_instances.at(it).frequency;
						}
						double total_pair_cnt = ins_freq_cnt1 * ins_freq_cnt2;
						for (int it = 0; it < object1_instances.size(); it++) {
							Instance ins1 = object1_instances.at(it);
							for (int it2 = 0; it2 < object2_instances.size(); it2++) {
								Instance ins2 = object2_instances.at(it2);
								double matched_prob = 0;
								for (int dim = 1; dim <= p_setting.dimension; dim++) {
									string A1 = ins1.attributes.at(dim - 1);
									string A2 = ins2.attributes.at(dim - 1);
									if (!p_setting.is_digits.at(dim - 1)) {
										//matched_prob += Jaccard_Similarity(A1, A2);
										matched_prob += 1 - Jaccard_Distance(A1, A2);
									}
									else {
										matched_prob += 1 - abs(stod(A1) - stod(A2));
									}
								}
								if (matched_prob > p_setting.gamma) {
									matched_pair_cnt = matched_pair_cnt + ins1.frequency * ins2.frequency;
								}
								//checked_pair_cnt = checked_pair_cnt + ins1.frequency * ins2.frequency;
							}

						}

						if (matched_pair_cnt / total_pair_cnt >= p_setting.alpha) {// pair matching, further checking whether or not topic-related
							bool is_topic_related = false;
							for (int it = 0; it < object1_instances.size(); it++) {
								for (int it2 = 1; it2 < p_setting.dimension; it2++) {
									for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
										if (object1_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
											is_topic_related = true;
											break;
										}
									}
									if (is_topic_related)
										break;
								}
								if (is_topic_related)
									break;
							}

							if (!is_topic_related) {
								for (int it = 0; it < object2_instances.size(); it++) {
									for (int it2 = 1; it2 < p_setting.dimension; it2++) {
										for (int it3 = 0; it3 < p_setting.keywords.size(); it3++) {
											if (object2_instances.at(it).attributes.at(it2 - 1).find(p_setting.keywords.at(it3)) != std::string::npos) {
												is_topic_related = true;
												break;
											}
										}
										if (is_topic_related)
											break;
									}
									if (is_topic_related)
										break;
								}
							}

							if (is_topic_related) {
								if (!check_existance(iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1), object_compared.ID)) {
									iDS.at(iDS_1 - 1).at(cur_time).matched_entities.at(iDS_2 - 1).push_back(object_compared.ID);
								}
								if (!check_existance(iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1), current_object.ID)) {
									iDS.at(iDS_2 - 1).at(time_temp).matched_entities.at(iDS_1 - 1).push_back(current_object.ID);
								}

							}
						}
					}

				}

			}

		}
	}

}

Parameter_Setting parameter_initialization(string setting_path) {
	Parameter_Setting p_setting;

	map<string, int> op_values = {
	{"file_cnt", 0},
	{"dimension", 1},
	{"gamma", 2},
	{"alpha", 3},
	{"xi", 4},
	{"cell_length", 5},
	{"entropyMin", 6},
	{"Ax_interval", 7},
	{"pvtCntMax", 8},
	{"parSize", 9},
	{"CDDNodeSize", 10},
	{"missing_attributes", 11},
	{"keywords", 12},
	{"is_digit", 13},
	{"file_path", 14},
	{"CDD_file", 15},
	{"Pivot_path", 16},
	{"tree_path", 17},
	{"converted_data_path", 18},
	{"ground_truth_path", 19},
	{"result_path", 20},
	{"qe_path", 21},
	{"method_ID", 22},
	{"Wt_ratio", 23},
	{"R_ratio", 24}
	};

	ifstream in(setting_path);


	string line, attribute;
	int attribute_cnt;
	int object_cnt = 0;

	istringstream iss;

	if (in)
	{
		while (getline(in, line))
		{
			iss.clear();
			iss.str(line);
			attribute_cnt = 0;// the number of retrieved attributes
			string option_key, value_temp;
			//char* path_temp;
			bool val_temp_bool;

			iss >> option_key;
			int op = op_values[option_key];
			switch (op)
			{
			case 0:
				iss >> value_temp;
				p_setting.file_cnt = stoi(value_temp);
				break;
			case 1:
				iss >> value_temp;
				p_setting.dimension = stoi(value_temp);
				break;
			case 2:
				iss >> value_temp;
				p_setting.gamma = stod(value_temp);
				break;
			case 3:
				iss >> value_temp;
				p_setting.alpha = stod(value_temp);
				break;
			case 4:
				iss >> value_temp;
				p_setting.xi = stod(value_temp);
				break;
			case 5:
				iss >> value_temp;
				p_setting.cell_length = stod(value_temp);
				break;
			case 6:
				iss >> value_temp;
				p_setting.entropyMin = stod(value_temp);
				break;
			case 7:
				iss >> value_temp;
				p_setting.Ax_interval = stod(value_temp);
				break;
			case 8:
				iss >> value_temp;
				p_setting.pvtCntMax = stoi(value_temp);
				break;
			case 9:
				iss >> value_temp;
				p_setting.parSize = stoi(value_temp);
				break;
			case 10:
				iss >> value_temp;
				p_setting.CDDNodeSize = stoi(value_temp);
				break;
			case 11:
				do {
					iss >> value_temp;
					if (!iss.fail()) {
						p_setting.missing_attributes.push_back(stoi(value_temp));
					}
				} while (!iss.fail());
				break;
			case 12:
				do {
					iss >> value_temp;
					if (!iss.fail()) {
						p_setting.keywords.push_back(value_temp);
					}
				} while (!iss.fail());
				break;
			case 13:
				do {
					iss >> value_temp;
					if (value_temp == "false")
						val_temp_bool = false;
					else
						val_temp_bool = true;
					if (!iss.fail()) {
						p_setting.is_digits.push_back(val_temp_bool);
					}
				} while (!iss.fail());
				break;
			case 14:
				do {
					iss >> value_temp;
					//path_temp = NULL;
					//path_temp = const_cast<char*>(value_temp.c_str());
					if (!iss.fail()) {
						p_setting.stream_paths.push_back(value_temp);
					}
				} while (!iss.fail());
				break;
			case 15:
				do {
					iss >> value_temp;
					//path_temp = const_cast<char*>(value_temp.c_str());
					if (!iss.fail()) {
						p_setting.CDD_paths.push_back(value_temp);
					}
				} while (!iss.fail());
				break;
			case 16:
				do {
					iss >> value_temp;
					//path_temp = const_cast<char*>(value_temp.c_str());
					if (!iss.fail()) {
						p_setting.pivot_paths.push_back(value_temp);
					}
				} while (!iss.fail());
				break;
			case 17:
				do {
					iss >> value_temp;
					//path_temp = const_cast<char*>(value_temp.c_str());
					if (!iss.fail()) {
						p_setting.tree_file_paths.push_back(value_temp);
					}
				} while (!iss.fail());
				break;
			case 18:
				do {
					iss >> value_temp;
					//path_temp = const_cast<char*>(value_temp.c_str());
					if (!iss.fail()) {
						p_setting.converted_file_paths.push_back(value_temp);
					}
				} while (!iss.fail());
				break;
			case 19:
				do {
					iss >> value_temp;
					//path_temp = const_cast<char*>(value_temp.c_str());
					if (!iss.fail()) {
						p_setting.ground_truth_paths.push_back(value_temp);
					}
				} while (!iss.fail());
				break;
			case 20:
				iss >> value_temp;
				//path_temp = const_cast<char*>(value_temp.c_str());
				p_setting.ER_result_path = value_temp;
				break;
			case 21:
				iss >> value_temp;
				//path_temp = const_cast<char*>(value_temp.c_str());
				p_setting.quality_evaluation_path = value_temp;
				break;
			case 22:
				iss >> value_temp;
				if(!value_temp.empty())
					p_setting.method_ID = stoi(value_temp);
				break;
			case 23:
				iss >> value_temp;
				p_setting.Wt_rate = stod(value_temp);
				break;
			case 24:
				iss >> value_temp;
				p_setting.R_ratio = stod(value_temp);
				break;
			default:
				break;
			}
		}
	}
	else
	{
		std::cout << "no such file" << endl;
	}

	in.close();


	return p_setting;
}

void ER_Query(vector<vector<Imputed_Data>> iDS, vector<vector<vector<CDD_Node>>> CDD_index, vector<vector<CDD_Rules>> CDDs, vector<vector<Data>>& data_repository, vector<vector<vector<string>>>& v_domains, vector<vector<R_Node>> R_Nodes, vector<Matching_Record> Ground_Truth, long double base_cost, long double base_cost2, Parameter_Setting p_setting) {
	int method_ID = p_setting.method_ID;
	long double cost_start, cost_end;
	long double query_cost, cost_per_pair;
	ofstream fout(p_setting.ER_result_path, ios::app);
	ofstream fout2(p_setting.quality_evaluation_path, ios::app);
	vector<Matching_Record> returned_results;
	switch (method_ID) {
	case 0:
		cost_start = clock();
		cout << "TER-iDS starts---------------" << endl;
		TER_iDS(iDS, CDD_index, CDDs, data_repository, v_domains, R_Nodes, p_setting);
		cout << "TER-iDS ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "TER-iDS time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for TER-iDS------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;
		fout.close();

		fout2 << "--------------quality evaluation for TER-iDS---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;
		fout2.close();
		break;
	case 1:
		cost_start = clock();
		cout << "Ij+GER starts---------------" << endl;
		Ij_GER(iDS, CDD_index, CDDs, data_repository, v_domains, R_Nodes, p_setting);
		cout << "Ij+GER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "Ij+GER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for Ij+GER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;
		fout.close();

		fout2 << "--------------quality evaluation for Ij+GER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;
		fout2.close();
		break;
	case 2:
		cost_start = clock();
		cout << "CDD+ER starts---------------" << endl;
		CDD_ER(iDS, data_repository, CDDs, p_setting);
		cout << "CDD+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "CDD+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for CDD+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;
		fout.close();

		fout2 << "--------------quality evaluation for CDD+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;
		fout2.close();
		break;
	case 3:
		cost_start = clock();
		cout << "DD+ER starts---------------" << endl;
		DD_ER(iDS, data_repository, CDDs, p_setting);
		cout << "DD+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "DD+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for DD+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;
		fout.close();

		fout2 << "--------------quality evaluation for DD+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;
		fout2.close();
		break;
	case 4:
		cost_start = clock();
		cout << "er+ER starts---------------" << endl;
		er_ER(iDS, data_repository, CDDs, p_setting);
		cout << "er+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "er+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for er+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;
		fout.close();

		fout2 << "--------------quality evaluation for er+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS, p_setting, cost_per_pair, base_cost2);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;
		fout2.close();
		break;
	case 5:
		cost_start = clock();
		cout << "con+ER starts---------------" << endl;
		con_ER(iDS, p_setting);
		cout << "con+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "con+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for con+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;
		fout.close();

		fout2 << "--------------quality evaluation for con+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS, p_setting, cost_per_pair, base_cost2);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;
		fout2.close();
		break;
	case -1:
		vector<vector<Imputed_Data>> iDS0 = iDS;
		cost_start = clock();
		cout << "TER-iDS starts---------------" << endl;
		TER_iDS(iDS0, CDD_index, CDDs, data_repository, v_domains, R_Nodes, p_setting);
		cout << "TER-iDS ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "TER-iDS time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for TER-iDS------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS0, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;

		fout2 << "--------------quality evaluation for TER-iDS---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS0, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;

		vector<vector<Imputed_Data>> iDS1 = iDS;
		cost_start = clock();
		cout << "Ij+GER starts---------------" << endl;
		Ij_GER(iDS1, CDD_index, CDDs, data_repository, v_domains, R_Nodes, p_setting);
		cout << "Ij+GER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "Ij+GER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for Ij+GER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS1, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;

		fout2 << "--------------quality evaluation for Ij+GER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS1, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;

		vector<vector<Imputed_Data>> iDS2 = iDS;
		cost_start = clock();
		cout << "CDD+ER starts---------------" << endl;
		CDD_ER(iDS2, data_repository, CDDs, p_setting);
		cout << "CDD+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "CDD+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for CDD+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS2, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;

		fout2 << "--------------quality evaluation for CDD+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS2, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;

		vector<vector<Imputed_Data>> iDS3 = iDS;
		cost_start = clock();
		cout << "DD+ER starts---------------" << endl;
		DD_ER(iDS3, data_repository, CDDs, p_setting);
		cout << "DD+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "DD+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for DD+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS3, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;

		fout2 << "--------------quality evaluation for DD+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS3, p_setting, cost_per_pair, base_cost);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;

		vector<vector<Imputed_Data>> iDS4 = iDS;
		cost_start = clock();
		cout << "er+ER starts---------------" << endl;
		er_ER(iDS4, data_repository, CDDs, p_setting);
		cout << "er+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "er+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for er+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS4, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;

		fout2 << "--------------quality evaluation for er+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS4, p_setting, cost_per_pair, base_cost2);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;

		vector<vector<Imputed_Data>> iDS5 = iDS;
		cost_start = clock();
		cout << "con+ER starts---------------" << endl;
		con_ER(iDS5, p_setting);
		cout << "con+ER ends---------------" << endl;
		cost_end = clock();
		query_cost = (cost_end - cost_start) / 1000;
		cout << "con+ER time cost is " << query_cost << endl;
		cost_per_pair = query_cost / pow(p_setting.object_max_size, 2);

		fout << "--------------matching results for con+ER------------------------" << endl << endl << endl << endl;
		cout << "write matching results to local file starts---------------" << endl;
		returned_results = write_ER_results(iDS5, p_setting);
		cout << "write matching results to local file ends---------------" << endl;
		fout << endl << endl << endl << endl;

		fout2 << "--------------quality evaluation for con+ER---------------" << endl << endl << endl << endl;
		cout << "quality evaluation starts---------------" << endl;
		quality_evaluation(returned_results, Ground_Truth, iDS5, p_setting, cost_per_pair, base_cost2);
		cout << "quality evaluation ends---------------" << endl;
		fout2 << endl << endl << endl << endl;
		fout.close();
		fout2.close();
		break;
	}

}


//--------------following codes need refinement----------------------


void main(int argc, char* argv[]) {
	/*
	Parameter_Setting p_setting;

	char* fileName = "GoogleProducts.csv";
	char* fileName2 = "Amazon.csv";

	char* CDD_file1 = "Google_CDD.txt";
	char* CDD_file2 = "Amazon_CDD.txt";

	char* pivot_file1 = "Google_pivots.txt";
	char* pivot_file2 = "Amazon_pivots.txt";

	char* tree_file1 = "Google_tree.txt";
	char* tree_file2 = "Amazon_tree.txt";

	char* converted_Data_File1 = "Google_converted_data.txt";
	char* converted_Data_File2 = "Amazon_converted_data.txt";

	char* ground_truth_file = "ground_truth.csv";

	char* ER_result_path = "ER_results.txt";
	char* quality_evaluation_path = "quality_evaluation.txt";

	int method_ID; 

	int dimension = 4;
	//int obj_cnt = 100;
	double gamma = 2;
	double alpha = 0.5;
	double xi = 0.1;
	double cell_length = 0.2;
	double entropyMin = 0.5;
	double Ax_interval = 0.1;
	int pvtCntMax = 1;
	int parSize = 5;
	int CDDNodeSize = 100;
	//int Wt_max_size = 1000000;

	vector<string> keywords;
	//keywords.push_back("adobe");
	//keywords.push_back("test");
	//keywords.push_back("human");
	keywords.push_back("contentbarrier");

	p_setting.is_digits.push_back(false);
	p_setting.is_digits.push_back(false);
	p_setting.is_digits.push_back(false);
	p_setting.is_digits.push_back(true);

	p_setting.dimension = dimension;
	p_setting.gamma = gamma;
	p_setting.alpha = alpha;
	p_setting.xi = xi;
	p_setting.Ax_interval = Ax_interval;
	p_setting.cell_length = cell_length;
	p_setting.entropyMin = entropyMin;
	p_setting.pvtCntMax = pvtCntMax;
	p_setting.parSize = parSize;
	p_setting.CDDNodeSize = CDDNodeSize;

	p_setting.stream_paths.push_back(fileName);
	p_setting.stream_paths.push_back(fileName2);

	p_setting.CDD_paths.push_back(CDD_file1);
	p_setting.CDD_paths.push_back(CDD_file2);

	p_setting.pivot_paths.push_back(pivot_file1);
	p_setting.pivot_paths.push_back(pivot_file2);

	p_setting.tree_file_paths.push_back(tree_file1);
	p_setting.tree_file_paths.push_back(tree_file2);

	p_setting.converted_file_paths.push_back(converted_Data_File1);
	p_setting.converted_file_paths.push_back(converted_Data_File2);

	p_setting.ground_truth_paths.push_back(ground_truth_file);

	p_setting.quality_evaluation_path = quality_evaluation_path;

	p_setting.ER_result_path = ER_result_path;

	p_setting.keywords = keywords;

	p_setting.missing_attributes.push_back(4);
	*/

	string setting_path = argv[1];
	//string setting_path = "setting_path.txt";
	Parameter_Setting p_setting = parameter_initialization(setting_path);
	p_setting.object_max_size = obtain_object_size(p_setting);
	//p_setting.Wt_size = p_setting.object_max_size;
	p_setting.Wt_size = p_setting.object_max_size * p_setting.Wt_rate;
	

	long double cost_start, cost_end;
	long double base_cost = 0;

	long double cost_start2, cost_end2;
	long double base_cost2 = 0;

	cost_start = clock();
	cost_start2 = clock();
	vector<vector<Data>> all_data = load_R(p_setting);
	cout << "data loaded---------------" << endl;

	norm_numeric(all_data, p_setting);
	cout << "data normalized---------------" << endl;

	cout << "obtain ground truth starts---------------" << endl;
	vector<Matching_Record> Ground_Truth = obtain_ground_truth(p_setting);
	cout << "obtain ground truth ends---------------" << endl;

	cout << "fill missing data via ground truth-------------" << endl;
	fill_via_ground_truth(all_data, Ground_Truth, p_setting);

	//vector<vector<Data>> data_repository = obtain_data_repository(all_data, p_setting);
	vector<vector<Data>> data_repository = all_data;
	cost_end2 = clock();
	base_cost2 += cost_end2 - cost_start2;

	cout << "domain obtain starts---------------" << endl;
	vector<vector<vector<string>>> v_domains = attribte_domain(data_repository, p_setting);
	cout << "domain obtain ends---------------" << endl;

	cout << "CDD rules mining starts---------------" << endl;
	vector<vector<CDD_Rules>> CDDs = obtain_CDDs(data_repository, v_domains, p_setting);
	cout << "CDD rules mining finish---------------" << endl;

	cout << "attribute pivots starts---------------" << endl;
	obtain_attribute_pivots(all_data, v_domains, p_setting);
	cout << "attribute pivots ends---------------" << endl;

	cout << "CDD index establishing starts---------------" << endl;
	vector<vector<vector<CDD_Node>>> CDD_index = establish_CDD_nodes(CDDs, p_setting);
	cout << "CDD index establishing ends---------------" << endl;

	cout << "data converting starts---------------" << endl;
	write_converted_data(data_repository, p_setting);
	cout << "data converting ends---------------" << endl;
	

	cout << "aR-tree nodes starts---------------" << endl;
	obtain_aRtree_nodes(p_setting);
	cout << "aR-tree nodes ends---------------" << endl << endl << endl << endl << endl << endl << endl << endl << endl << endl << endl << endl << endl << endl << endl << endl;

	cout << "aR-tree nodes aggregates starts---------------" << endl;
	vector<vector<R_Node>> R_nodes = obtain_node_information_for_R(all_data, p_setting);
	cout << "aR-tree nodes aggregates ends---------------" << endl;


	//cout << which_node(p_setting.tree_roots.at(1), 1410) << endl;

	cost_start2 = clock();
	cout << "imputed data stream intialization starts---------------" << endl;
	vector<vector<Imputed_Data>> iDS = imputed_Data_Initialization(all_data, p_setting);
	cout << "imputed data stream intialization ends---------------" << endl;
	cost_end = clock();
	cost_end2 = clock();
	base_cost += cost_end - cost_start;
	base_cost /= (1000 * pow(p_setting.object_max_size, 2));// add this cost for CDD-related baselines

	base_cost2 += cost_end2 - cost_start2; 
	base_cost2 /= (1000 * pow(p_setting.object_max_size, 2));// add this cost for other baselines

	//cout << "imputed data initialization time cost is " << (cost_end - cost_start) / 1000 << endl;
	//double cost_per_pair = (cost_end - cost_start) / (1000 * pow(p_setting.object_max_size, 2));
	//cout << "time cost per entity pair --> " << cost_per_pair << endl;



	/*
	cost_start = clock();
	cout << "TER-iDS starts---------------" << endl;
	TER_iDS(iDS, CDD_index, CDDs, data_repository, v_domains, R_nodes, p_setting);
	//CDD_ER(iDS, data_repository, CDDs, p_setting);
	//Ij_GER(iDS, CDD_index, CDDs, data_repository, v_domains, R_nodes, p_setting);
	//DD_ER(iDS, data_repository, CDDs, p_setting);
	//con_ER(iDS, p_setting);
	//er_ER(iDS, data_repository, CDDs, p_setting);
	cout << "TER-iDS ends---------------" << endl;
	cost_end = clock();
	cout << "TER-iDS time cost is " << (cost_end - cost_start) / 1000 << endl;

	cost_start = clock();
	cout << "write matching results to local file starts---------------" << endl;
	vector<Matching_Record> returned_results = write_ER_results(iDS, p_setting);
	cout << "write matching results to local file ends---------------" << endl;
	cost_end = clock();
	cout << "TER-iDS result writing time cost is " << (cost_end - cost_start) / 1000 << endl;
	
	cout << "quality evaluation starts---------------" << endl;
	quality_evaluation(returned_results, Ground_Truth, iDS, p_setting, cost_per_pair);
	cout << "quality evaluation ends---------------" << endl;
	*/

	ER_Query(iDS, CDD_index, CDDs, data_repository, v_domains, R_nodes, Ground_Truth, base_cost, base_cost2, p_setting);

	system("pause");
}