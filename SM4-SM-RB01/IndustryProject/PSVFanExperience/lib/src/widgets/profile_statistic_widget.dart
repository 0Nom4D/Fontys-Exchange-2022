import 'package:flutter/material.dart';
import 'package:psv_fan_experience/src/models/profile_statistic.dart';

class ProfileStatisticWidget extends StatelessWidget {
  final ProfileStatistic profileStatistic;

  const ProfileStatisticWidget({super.key, required this.profileStatistic});

  @override
  Widget build(BuildContext context) {
    return Column(
      children: [
        Text(
          profileStatistic.value.toString(),
          style: const TextStyle(
            fontSize: 34,
            fontWeight: FontWeight.bold,
            color: Colors.black,
          ),
        ),
        Text(
          profileStatistic.label.toUpperCase(),
          style: const TextStyle(
            fontSize: 14,
            fontWeight: FontWeight.bold,
            color: Colors.white,
          ),
        )
      ],
    );
  }
}
