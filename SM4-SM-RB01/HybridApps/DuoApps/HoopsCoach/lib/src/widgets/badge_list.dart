import 'package:flutter/material.dart';

import 'package:app/src/widgets/badge_image.dart';
import 'package:app/src/models/achievements.dart';

class BadgeList extends StatelessWidget {
  const BadgeList({required this.title, required this.achievements, super.key});

  final String title;
  final List<Achievement> achievements;

  @override
  Widget build(BuildContext context) {
    return Padding(
      padding: const EdgeInsets.all(4.0),
      child: Column(
        crossAxisAlignment: CrossAxisAlignment.start,
        children: [
          Text(
            title,
            textAlign: TextAlign.left,
            style: const TextStyle(
              color: Colors.white,
              fontSize: 25,
              fontWeight: FontWeight.bold,
              fontStyle: FontStyle.italic
            ),
          ),
          const SizedBox(height: 10),
          SizedBox(
            height: MediaQuery.of(context).size.height * .1375,
            child: GridView.count(
              scrollDirection: Axis.horizontal,
              crossAxisCount: 1,
              crossAxisSpacing: 10,
              mainAxisSpacing: 10,
              children: <Widget>[
                for (var achievement in achievements)
                  BadgeImage.from(achievement, false)
              ]
            ),
          )
        ],
      ),
    );
  }
}
