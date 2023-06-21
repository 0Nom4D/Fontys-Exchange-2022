import 'package:flutter/material.dart';

class AnalysisItem{
  AnalysisItem({
    required this.name,
    required this.icon,
  });

  String name;
  IconData icon;

  static AnalysisItem video = AnalysisItem(name: 'Shoot Analysis', icon: Icons.video_collection);
  static AnalysisItem image = AnalysisItem(name: 'Posture Analysis', icon: Icons.image);

  static List<AnalysisItem> analysisKinds = [video, image];

  static Widget buildItem(AnalysisItem item) {
    return Row(
      children: [
        Icon(item.icon, color: Colors.white, size: 22),
        const SizedBox(
          width: 10,
        ),
        Text(
          item.name,
          style: const TextStyle(
            color: Colors.white,
          ),
        ),
      ],
    );
  }
}