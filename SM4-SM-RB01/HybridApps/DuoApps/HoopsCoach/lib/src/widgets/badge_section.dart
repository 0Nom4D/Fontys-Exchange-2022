import 'package:flutter/material.dart';

import 'package:provider/provider.dart';

import 'package:app/src/providers/achievements_provider.dart';
import 'package:app/src/widgets/badge_image.dart';

class BadgeSection extends StatelessWidget {
  const BadgeSection({super.key});

  @override
  Widget build(BuildContext context) {
    AchievementProvider provider = Provider.of<AchievementProvider>(context, listen: false);

    return Padding(
      padding: const EdgeInsets.all(8.0),
      child: Column(
        crossAxisAlignment: CrossAxisAlignment.start,
        children: [
          const Text(
            "Badges",
            textAlign: TextAlign.left,
            style: TextStyle(
              color: Colors.white,
              fontSize: 25,
              fontWeight: FontWeight.bold
            ),
          ),
          const Text(
            "Earn badges by completing this exercise",
            textAlign: TextAlign.left,
            style: TextStyle(
              color: Colors.grey,
              fontSize: 15,
            ),
          ),
          Padding(
            padding: const EdgeInsets.symmetric(vertical: 8.0),
            child: BadgeImage.from(provider.achievements.first, true),
          )
        ],
      ),
    );
  }
}
